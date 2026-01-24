//! Integration tests for the heap module with BufferPool.
//!
//! These tests verify that HeapPage, Record, and Value work correctly
//! when used with the BufferPool's page guards.

use enhance::heap::{HeapPage, Record, Value};
use enhance::protocol::type_oid;
use enhance::storage::{BufferPool, LruReplacer, MemoryStorage};

#[tokio::test]
async fn test_slotted_page_with_buffer_pool() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    // Create a new page
    let mut guard = pool.new_page().await.unwrap();
    let page_id = guard.page_id();

    // Initialize as slotted page and insert raw bytes
    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();

        let slot0 = page.insert(b"hello").unwrap();
        let slot1 = page.insert(b"world").unwrap();

        assert_eq!(slot0, 0);
        assert_eq!(slot1, 1);
        assert_eq!(page.record_count(), 2);
    }
    guard.mark_dirty();
    drop(guard);

    // Read back using read-only guard
    let guard = pool.fetch_page(page_id).await.unwrap();
    let page = HeapPage::new(guard.data());

    assert_eq!(page.read(0), Some(b"hello".as_slice()));
    assert_eq!(page.read(1), Some(b"world".as_slice()));
    assert_eq!(page.record_count(), 2);
}

#[tokio::test]
async fn test_record_serialization_with_buffer_pool() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    let schema = [type_oid::INT4, type_oid::TEXT, type_oid::BOOL];

    // Create and insert records
    let mut guard = pool.new_page().await.unwrap();
    let page_id = guard.page_id();

    let records = vec![
        Record::new(vec![
            Value::Int32(1),
            Value::Text("first".to_string()),
            Value::Boolean(true),
        ]),
        Record::new(vec![
            Value::Int32(2),
            Value::Text("second".to_string()),
            Value::Boolean(false),
        ]),
        Record::new(vec![
            Value::Int32(3),
            Value::Null,
            Value::Boolean(true),
        ]),
    ];

    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();

        for record in &records {
            let mut buf = vec![0u8; record.serialized_size()];
            record.serialize(&mut buf).unwrap();
            page.insert(&buf).unwrap();
        }
    }
    guard.mark_dirty();
    drop(guard);

    // Read back and deserialize
    let guard = pool.fetch_page(page_id).await.unwrap();
    let page = HeapPage::new(guard.data());

    let parsed_records: Vec<Record> = page
        .iter()
        .map(|(_, data)| Record::deserialize(data, &schema).unwrap())
        .collect();

    assert_eq!(parsed_records, records);
}

#[tokio::test]
async fn test_update_record_in_buffer_pool() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    // Create page and insert initial record
    let mut guard = pool.new_page().await.unwrap();
    let page_id = guard.page_id();

    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();
        page.insert(b"initial").unwrap();
    }
    guard.mark_dirty();
    drop(guard);

    // Update the record
    let mut guard = pool.fetch_page_mut(page_id).await.unwrap();
    {
        let mut page = HeapPage::new(guard.data_mut());
        page.update(0, b"updated value").unwrap();
    }
    guard.mark_dirty();
    drop(guard);

    // Verify update
    let guard = pool.fetch_page(page_id).await.unwrap();
    let page = HeapPage::new(guard.data());
    assert_eq!(page.read(0), Some(b"updated value".as_slice()));
}

#[tokio::test]
async fn test_delete_and_compact_with_buffer_pool() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    let mut guard = pool.new_page().await.unwrap();
    let page_id = guard.page_id();

    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();

        page.insert(b"record0").unwrap();
        page.insert(b"record1").unwrap();
        page.insert(b"record2").unwrap();

        // Delete middle record
        page.delete(1).unwrap();

        // Verify fragmentation exists
        assert!(page.fragmentation() > 0.0);

        // Compact
        page.compact();

        // Fragmentation should be gone
        assert!(page.fragmentation() < 0.01);

        // Remaining records should be intact
        assert_eq!(page.read(0), Some(b"record0".as_slice()));
        assert!(page.read(1).is_none());
        assert_eq!(page.read(2), Some(b"record2".as_slice()));
    }
    guard.mark_dirty();
    drop(guard);

    // Verify persistence
    let guard = pool.fetch_page(page_id).await.unwrap();
    let page = HeapPage::new(guard.data());
    assert_eq!(page.record_count(), 2);
}

#[tokio::test]
async fn test_multiple_pages() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    let mut page_ids = Vec::new();

    // Create multiple pages with records
    for i in 0..5 {
        let mut guard = pool.new_page().await.unwrap();
        page_ids.push(guard.page_id());

        {
            let mut page = HeapPage::new(guard.data_mut());
            page.init();
            page.insert(format!("page {} record", i).as_bytes()).unwrap();
        }
        guard.mark_dirty();
    }

    // Verify all pages
    for (i, &page_id) in page_ids.iter().enumerate() {
        let guard = pool.fetch_page(page_id).await.unwrap();
        let page = HeapPage::new(guard.data());
        let expected = format!("page {} record", i);
        assert_eq!(page.read(0), Some(expected.as_bytes()));
    }
}

#[tokio::test]
async fn test_page_eviction_and_reload() {
    // Small pool to force eviction
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(3);
    let pool = BufferPool::new(storage, replacer, 3);

    let mut page_ids = Vec::new();

    // Create more pages than pool size
    for i in 0..10 {
        let mut guard = pool.new_page().await.unwrap();
        page_ids.push(guard.page_id());

        {
            let mut page = HeapPage::new(guard.data_mut());
            page.init();

            let record = Record::new(vec![Value::Int32(i as i32)]);
            let mut buf = vec![0u8; record.serialized_size()];
            record.serialize(&mut buf).unwrap();
            page.insert(&buf).unwrap();
        }
        guard.mark_dirty();
    }

    // Verify all pages can still be read (some will be reloaded from storage)
    let schema = [type_oid::INT4];
    for (i, &page_id) in page_ids.iter().enumerate() {
        let guard = pool.fetch_page(page_id).await.unwrap();
        let page = HeapPage::new(guard.data());

        let data = page.read(0).expect("record should exist");
        let record = Record::deserialize(data, &schema).unwrap();

        assert_eq!(record.values[0], Value::Int32(i as i32));
    }
}

#[tokio::test]
async fn test_large_records_fill_page() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    let mut guard = pool.new_page().await.unwrap();
    let page_id = guard.page_id();

    let large_text = "x".repeat(1000);
    let schema = [type_oid::TEXT];

    let mut inserted_count = 0;
    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();

        loop {
            let record = Record::new(vec![Value::Text(large_text.clone())]);
            let mut buf = vec![0u8; record.serialized_size()];
            record.serialize(&mut buf).unwrap();

            if page.insert(&buf).is_err() {
                break;
            }
            inserted_count += 1;
        }
    }
    guard.mark_dirty();
    drop(guard);

    // Should have inserted multiple large records
    assert!(inserted_count > 0);

    // Verify all records
    let guard = pool.fetch_page(page_id).await.unwrap();
    let page = HeapPage::new(guard.data());

    for (slot_id, data) in page.iter() {
        let record = Record::deserialize(data, &schema).unwrap();
        assert_eq!(record.values[0], Value::Text(large_text.clone()));
        assert!(slot_id < inserted_count as u16);
    }
    assert_eq!(page.record_count(), inserted_count);
}

#[tokio::test]
async fn test_slot_reuse_after_delete() {
    let storage = MemoryStorage::new();
    let replacer = LruReplacer::new(10);
    let pool = BufferPool::new(storage, replacer, 10);

    let mut guard = pool.new_page().await.unwrap();

    {
        let mut page = HeapPage::new(guard.data_mut());
        page.init();

        // Insert 3 records
        page.insert(b"a").unwrap();
        page.insert(b"b").unwrap();
        page.insert(b"c").unwrap();

        // Delete first and second
        page.delete(0).unwrap();
        page.delete(1).unwrap();

        // Insert new record - should reuse slot 1 (most recently deleted, LIFO order)
        let slot = page.insert(b"new").unwrap();
        assert_eq!(slot, 1);

        // Insert another - should reuse slot 0
        let slot = page.insert(b"newer").unwrap();
        assert_eq!(slot, 0);

        // Verify contents
        assert_eq!(page.read(0), Some(b"newer".as_slice()));
        assert_eq!(page.read(1), Some(b"new".as_slice()));
        assert_eq!(page.read(2), Some(b"c".as_slice()));
    }
    guard.mark_dirty();
}
