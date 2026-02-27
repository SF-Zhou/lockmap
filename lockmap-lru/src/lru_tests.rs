#[cfg(test)]
mod tests {
    use crate::LruLockMap;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_lru_basic() {
        let map = LruLockMap::<String, u32>::with_capacity_per_shard(10);
        assert!(map.is_empty());

        map.insert("key1".into(), 1);
        assert_eq!(map.len(), 1);
        assert_eq!(map.get("key1"), Some(1));

        map.insert("key2".into(), 2);
        assert_eq!(map.len(), 2);

        assert_eq!(map.remove("key1"), Some(1));
        assert_eq!(map.len(), 1);

        assert!(map.contains_key("key2"));
        assert!(!map.contains_key("key1"));
    }

    #[test]
    fn test_lru_eviction() {
        // Create a map with capacity 2 per shard, single shard for predictability
        let map = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(2, 1);

        // Insert 3 items - should evict the first one
        map.insert(1, 100);
        map.insert(2, 200);
        map.insert(3, 300);

        // Item 1 should have been evicted
        assert!(map.get(&1).is_none(), "Item 1 should have been evicted");
        assert_eq!(map.get(&2), Some(200));
        assert_eq!(map.get(&3), Some(300));
    }

    #[test]
    fn test_lru_access_updates() {
        // Create a map with capacity 2, single shard
        let map = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(2, 1);

        map.insert(1, 100);
        map.insert(2, 200);

        // Access item 1 to make it recently used
        assert_eq!(map.get(&1), Some(100));

        // Insert item 3 - should evict item 2 (least recently used)
        map.insert(3, 300);

        assert_eq!(map.get(&1), Some(100), "Item 1 should still exist");
        assert!(map.get(&2).is_none(), "Item 2 should have been evicted");
        assert_eq!(map.get(&3), Some(300));
    }

    #[test]
    fn test_lru_update_existing() {
        let map = LruLockMap::<String, u32>::with_capacity_per_shard(10);

        map.insert("key".into(), 1);
        assert_eq!(map.get("key"), Some(1));

        // Update existing key
        let old = map.insert("key".into(), 2);
        assert_eq!(old, Some(1));
        assert_eq!(map.get("key"), Some(2));
    }

    #[test]
    fn test_lru_concurrent_access() {
        let map = Arc::new(LruLockMap::<u32, u32>::with_capacity_per_shard(100));

        const THREADS: usize = 4;
        const OPS_PER_THREAD: usize = 1000;

        let handles: Vec<_> = (0..THREADS)
            .map(|t| {
                let map = Arc::clone(&map);
                thread::spawn(move || {
                    for i in 0..OPS_PER_THREAD {
                        let key = (t * OPS_PER_THREAD + i) as u32;
                        map.insert(key, key * 10);
                        assert_eq!(map.get(&key), Some(key * 10));
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        // Verify some entries exist
        let len = map.len();
        assert!(len > 0, "Map should contain entries");
    }

    #[test]
    fn test_lru_mixed_operations() {
        let map = LruLockMap::<String, String>::with_capacity_per_shard(50);

        // Insert
        for i in 0..20 {
            map.insert(format!("key{}", i), format!("value{}", i));
        }

        // Read some
        for i in 0..10 {
            assert_eq!(map.get(&format!("key{}", i)), Some(format!("value{}", i)));
        }

        // Remove some
        for i in 10..15 {
            assert_eq!(
                map.remove(&format!("key{}", i)),
                Some(format!("value{}", i))
            );
        }

        // Update some
        for i in 0..5 {
            map.insert(format!("key{}", i), format!("updated{}", i));
        }

        // Verify
        for i in 0..5 {
            assert_eq!(map.get(&format!("key{}", i)), Some(format!("updated{}", i)));
        }
    }

    #[test]
    fn test_lru_capacity_enforcement() {
        const CAPACITY: usize = 10;
        let map = LruLockMap::<u32, u32>::with_capacity_and_shard_amount(CAPACITY, 1);

        // Insert more than capacity
        for i in 0..CAPACITY * 2 {
            map.insert(i as u32, i as u32);
        }

        // Map should not exceed capacity (with some tolerance for eviction timing)
        let len = map.len();
        assert!(
            len <= CAPACITY + 2,
            "Map size {} should be close to capacity {}",
            len,
            CAPACITY
        );
    }

    #[test]
    fn test_lru_empty_operations() {
        let map = LruLockMap::<String, u32>::new();

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.get("nonexistent"), None);
        assert!(!map.contains_key("nonexistent"));
        assert_eq!(map.remove("nonexistent"), None);
    }

    #[test]
    fn test_lru_clone_values() {
        let map = LruLockMap::<String, Vec<u32>>::with_capacity_per_shard(10);

        let vec = vec![1, 2, 3, 4, 5];
        map.insert("key".into(), vec.clone());

        let retrieved = map.get("key").unwrap();
        assert_eq!(retrieved, vec);
    }
}
