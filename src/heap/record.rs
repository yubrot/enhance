//! Record representation and serialization.
//!
//! A [`Record`] represents the data portion of a database row, consisting of multiple
//! [`Value`](crate::datum::Value)s. Records can be serialized to a compact binary format for storage.
//!
//! ## Relationship to Tuples
//!
//! In the storage layer:
//! - **Tuple** = TupleHeader (MVCC metadata) + Record (data values)
//! - **Record** = Just the data values (Vec<Value>), without MVCC information
//!
//! Records are combined with TupleHeaders when stored in heap pages to form complete tuples.

use crate::datum::{SerializationError, Type, Value};
use crate::ensure_buf_len;

/// A record (row of data values).
///
/// This represents the data portion of a row, without MVCC metadata (TupleHeader).
/// When combined with a TupleHeader, a Record forms a complete tuple in storage.
/// Use [`serialize`](Self::serialize) to convert to on-disk format.
///
/// # Serialization Format
///
/// ```text
/// +---------------------------+
/// | Null Bitmap (ceil(n/8) B) |  bit=1: NOT NULL, bit=0: NULL
/// +---------------------------+
/// | Value[0] (if not null)    |
/// | Value[1] (if not null)    |
/// | ...                       |
/// +---------------------------+
/// ```
///
/// # Example
///
/// ```no_run
/// use enhance::datum::{Type, Value};
/// use enhance::heap::Record;
///
/// let record = Record::new(vec![
///     Value::Int32(42),
///     Value::Text("hello".to_string()),
///     Value::Null,
/// ]);
///
/// let mut buf = vec![0u8; record.serialized_size()];
/// record.serialize(&mut buf).unwrap();
///
/// let schema = [Type::Int4, Type::Text, Type::Int4];
/// let parsed = Record::deserialize(&buf, &schema).unwrap();
/// assert_eq!(parsed, record);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Record {
    /// Column values in order.
    pub values: Vec<Value>,
}

impl Record {
    /// Creates a new record with the given values.
    pub fn new(values: Vec<Value>) -> Self {
        Self { values }
    }

    /// Returns the number of columns.
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns true if the record has no columns.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returns the serialized size of this record in bytes.
    ///
    /// This includes the null bitmap and all non-null values.
    pub fn serialized_size(&self) -> usize {
        let null_bitmap_bytes = self.values.len().div_ceil(8);
        let values_size: usize = self.values.iter().map(|v| v.serialized_size()).sum();
        null_bitmap_bytes + values_size
    }

    /// Serializes this record to a buffer.
    ///
    /// Returns the number of bytes written.
    ///
    /// # Errors
    ///
    /// Returns `SerializationError::BufferTooSmall` if the buffer is too small.
    pub fn serialize(&self, buf: &mut [u8]) -> Result<usize, SerializationError> {
        let required = self.serialized_size();
        ensure_buf_len!(buf, required);

        let num_cols = self.values.len();
        let null_bitmap_bytes = num_cols.div_ceil(8);

        // Write null bitmap (bit=1 means NOT NULL)
        for (i, byte) in buf.iter_mut().take(null_bitmap_bytes).enumerate() {
            let mut b = 0u8;
            for bit in 0..8 {
                let col_idx = i * 8 + bit;
                if col_idx < num_cols && !self.values[col_idx].is_null() {
                    b |= 1 << bit;
                }
            }
            *byte = b;
        }

        // Write values (null values write 0 bytes)
        let mut offset = null_bitmap_bytes;
        for value in &self.values {
            offset += value.serialize(&mut buf[offset..])?;
        }

        Ok(offset)
    }

    /// Deserializes a record from a buffer.
    ///
    /// # Arguments
    ///
    /// * `buf` - Source buffer containing serialized record data
    /// * `schema` - Column data types (needed to parse each value)
    ///
    /// # Errors
    ///
    /// Returns error if buffer is malformed or too small.
    pub fn deserialize(buf: &[u8], schema: &[Type]) -> Result<Self, SerializationError> {
        let num_cols = schema.len();
        let null_bitmap_bytes = num_cols.div_ceil(8);
        ensure_buf_len!(buf, null_bitmap_bytes);

        // Read null bitmap
        let is_null: Vec<bool> = (0..num_cols)
            .map(|i| {
                let byte_idx = i / 8;
                let bit_idx = i % 8;
                // bit=1 means NOT NULL, so is_null when bit=0
                (buf[byte_idx] & (1 << bit_idx)) == 0
            })
            .collect();

        // Read values
        let mut offset = null_bitmap_bytes;
        let mut values = Vec::with_capacity(num_cols);

        for (i, &ty) in schema.iter().enumerate() {
            if is_null[i] {
                values.push(Value::Null);
            } else {
                let (value, bytes_read) = Value::deserialize(&buf[offset..], ty)?;
                values.push(value);
                offset += bytes_read;
            }
        }

        Ok(Record { values })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_record() {
        let record = Record::new(vec![]);
        assert!(record.is_empty());
        assert_eq!(record.len(), 0);
        assert_eq!(record.serialized_size(), 0);

        let mut buf = vec![0u8; 0];
        let written = record.serialize(&mut buf).unwrap();
        assert_eq!(written, 0);

        let parsed = Record::deserialize(&buf, &[]).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_single_value_record() {
        let record = Record::new(vec![Value::Int32(42)]);
        assert_eq!(record.len(), 1);
        // 1 byte null bitmap + 4 bytes int32
        assert_eq!(record.serialized_size(), 1 + 4);

        let mut buf = vec![0u8; record.serialized_size()];
        let written = record.serialize(&mut buf).unwrap();
        assert_eq!(written, 5);

        let schema = [Type::Int4];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_multiple_values_record() {
        let record = Record::new(vec![
            Value::Int32(42),
            Value::Text("hello".to_string()),
            Value::Boolean(true),
        ]);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [Type::Int4, Type::Text, Type::Bool];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_record_with_nulls() {
        let record = Record::new(vec![
            Value::Int32(42),
            Value::Null,
            Value::Text("hello".to_string()),
            Value::Null,
        ]);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [Type::Int4, Type::Text, Type::Text, Type::Int4];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_all_null_record() {
        let record = Record::new(vec![Value::Null, Value::Null, Value::Null]);
        // Only null bitmap, no values
        assert_eq!(record.serialized_size(), 1);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [Type::Int4, Type::Text, Type::Bool];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_null_bitmap_multiple_bytes() {
        // 9 columns require 2 bytes for null bitmap, with mixed nulls
        let record = Record::new(vec![
            Value::Int32(1),
            Value::Null,
            Value::Int32(3),
            Value::Null,
            Value::Int32(5),
            Value::Null,
            Value::Int32(7),
            Value::Null,
            Value::Int32(9),
        ]);

        // 2 bytes bitmap + 5 * 4 bytes = 22 bytes
        assert_eq!(record.serialized_size(), 2 + 20);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = vec![Type::Int4; 9];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_all_types() {
        let record = Record::new(vec![
            Value::Boolean(true),
            Value::Int16(i16::MAX),
            Value::Int32(i32::MAX),
            Value::Int64(i64::MAX),
            Value::Float32(std::f32::consts::PI),
            Value::Float64(std::f64::consts::PI),
            Value::Text("hello".to_string()),
            Value::Bytea(vec![1, 2, 3]),
        ]);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [
            Type::Bool,
            Type::Int2,
            Type::Int4,
            Type::Int8,
            Type::Float4,
            Type::Float8,
            Type::Text,
            Type::Bytea,
        ];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_buffer_too_small_for_record() {
        let record = Record::new(vec![Value::Int32(42)]);
        let mut buf = vec![0u8; 2]; // Need 5 bytes

        let result = record.serialize(&mut buf);
        assert!(matches!(
            result,
            Err(SerializationError::BufferTooSmall { required: 5, .. })
        ));
    }

    #[test]
    fn test_deserialize_buffer_too_small() {
        let buf = vec![0u8; 0];
        let schema = [Type::Int4];

        let result = Record::deserialize(&buf, &schema);
        assert!(matches!(
            result,
            Err(SerializationError::BufferTooSmall {
                required: 1,
                available: 0
            })
        ));
    }

    #[test]
    fn test_large_text_record() {
        let large_text = "x".repeat(10000);
        let record = Record::new(vec![Value::Text(large_text.clone())]);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [Type::Text];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }

    #[test]
    fn test_unicode_text() {
        let record = Record::new(vec![Value::Text("日本語🎉emoji".to_string())]);

        let mut buf = vec![0u8; record.serialized_size()];
        record.serialize(&mut buf).unwrap();

        let schema = [Type::Text];
        let parsed = Record::deserialize(&buf, &schema).unwrap();
        assert_eq!(parsed, record);
    }
}
