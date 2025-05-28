use foldhash::fast::{FixedState, RandomState};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};
use std::sync::Mutex;

/// Represents the action to be taken on a value in the `ShardMap`.
pub enum SimpleAction {
    /// Keep the current value unchanged.
    Keep,
    /// Remove the value from the map.
    Remove,
}

/// Represents the action to be taken on a value in the `ShardMap`.
pub enum UpdateAction<V> {
    /// Keep the current value unchanged.
    Keep,
    /// Update the value with the provided new value.
    Replace(V),
}

/// A thread-safe hashmap shard.
///
/// This struct wraps a `HashMap` protected by a `Mutex` to ensure thread safety.
#[derive(Debug)]
pub struct ShardMap<K, V> {
    /// The underlying hashmap protected by a `Mutex`.
    map: Mutex<HashMap<K, V, RandomState>>,
}

impl<K, V> ShardMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new `ShardMap` with the specified initial capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The initial capacity of the hashmap.
    ///
    /// # Returns
    ///
    /// A new `ShardMap` instance.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: Mutex::new(HashMap::with_capacity_and_hasher(
                capacity,
                RandomState::default(),
            )),
        }
    }

    pub fn len(&self) -> usize {
        self.map.lock().unwrap().len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.lock().unwrap().is_empty()
    }

    pub fn simple_update<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(Option<&mut V>) -> (SimpleAction, R),
    {
        let mut map = self.map.lock().unwrap();
        let value = map.get_mut(key);
        let has_value = value.is_some();
        let (action, ret) = func(value);
        if has_value && matches!(action, SimpleAction::Remove) {
            let _ = map.remove_entry(key);
        }
        ret
    }

    /// Updates the value associated with the given key using the provided function.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to update.
    /// * `func` - A function that takes an `Option<&mut V>` and returns a tuple containing the action to take and the result.
    ///
    /// # Returns
    ///
    /// The result returned by the provided function.
    pub fn update<F, R>(&self, key: K, func: F) -> R
    where
        F: FnOnce(Option<&mut V>) -> (UpdateAction<V>, R),
    {
        let mut map = self.map.lock().unwrap();
        match map.get_mut(&key) {
            Some(value) => {
                let (action, ret) = func(Some(value));
                match action {
                    UpdateAction::Keep => {}
                    UpdateAction::Replace(v) => {
                        *value = v;
                    }
                }
                ret
            }
            None => {
                let (action, ret) = func(None);
                match action {
                    UpdateAction::Keep => {}
                    UpdateAction::Replace(value) => {
                        map.insert(key, value);
                    }
                }
                ret
            }
        }
    }

    /// Updates the value associated with the given key using the provided function.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to update.
    /// * `func` - A function that takes an `Option<&mut V>` and returns a tuple containing the action to take and the result.
    ///
    /// # Returns
    ///
    /// The result returned by the provided function.
    pub fn update_by_ref<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(Option<&mut V>) -> (UpdateAction<V>, R),
    {
        let mut map = self.map.lock().unwrap();
        match map.get_mut(key) {
            Some(value) => {
                let (action, ret) = func(Some(value));
                match action {
                    UpdateAction::Keep => {}
                    UpdateAction::Replace(v) => {
                        *value = v;
                    }
                }
                ret
            }
            None => {
                let (action, ret) = func(None);
                match action {
                    UpdateAction::Keep => {}
                    UpdateAction::Replace(value) => {
                        map.insert(key.into(), value);
                    }
                }
                ret
            }
        }
    }
}

/// A collection of `ShardMap` instances, providing sharded access to a hashmap.
pub struct ShardsMap<K, V> {
    /// The vector of `ShardMap` instances.
    shards: Vec<ShardMap<K, V>>,
}

impl<K, V> ShardsMap<K, V>
where
    K: Eq + Hash,
{
    /// Creates a new `ShardsMap` with the specified capacity and number of shards.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The total initial capacity of the hashmap.
    /// * `shard_amount` - The number of shards to create.
    ///
    /// # Returns
    ///
    /// A new `ShardsMap` instance.
    pub fn with_capacity_and_shard_amount(capacity: usize, shard_amount: usize) -> Self {
        let shard_capacity = capacity / shard_amount;
        Self {
            shards: (0..shard_amount)
                .map(|_| ShardMap::with_capacity(shard_capacity))
                .collect::<Vec<_>>(),
        }
    }

    pub fn len(&self) -> usize {
        self.shards.iter().map(|s| s.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.is_empty())
    }

    /// Updates the value associated with the given key using the provided function.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to update.
    /// * `func` - A function that takes an `Option<&mut V>` and returns a tuple containing the action to take and the result.
    ///
    /// # Returns
    ///
    /// The result returned by the provided function.
    pub fn simple_update<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(Option<&mut V>) -> (SimpleAction, R),
    {
        self.shard(key).simple_update(key, func)
    }

    /// Updates the value associated with the given key using the provided function.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to update.
    /// * `func` - A function that takes an `Option<&mut V>` and returns a tuple containing the action to take and the result.
    ///
    /// # Returns
    ///
    /// The result returned by the provided function.
    pub fn update<F, R>(&self, key: K, func: F) -> R
    where
        F: FnOnce(Option<&mut V>) -> (UpdateAction<V>, R),
    {
        self.shard(&key).update(key, func)
    }

    /// Updates the value associated with the given key using the provided function.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to update.
    /// * `func` - A function that takes an `Option<&mut V>` and returns a tuple containing the action to take and the result.
    ///
    /// # Returns
    ///
    /// The result returned by the provided function.
    pub fn update_by_ref<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q> + for<'c> From<&'c Q>,
        Q: Eq + Hash + ?Sized,
        F: FnOnce(Option<&mut V>) -> (UpdateAction<V>, R),
    {
        self.shard(key).update_by_ref(key, func)
    }

    #[inline(always)]
    fn shard<Q>(&self, key: &Q) -> &ShardMap<K, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let idx = FixedState::default().hash_one(key) as usize % self.shards.len();
        &self.shards[idx]
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicU32, Ordering},
        Arc,
    };

    use super::*;

    #[test]
    fn test_shards_map() {
        let shards_map = ShardsMap::<u32, u32>::with_capacity_and_shard_amount(256, 16);
        assert!(shards_map.is_empty());
        assert_eq!(shards_map.len(), 0);
        shards_map.update(1, |v| {
            assert_eq!(v, None);
            (UpdateAction::Replace(1), ())
        });
        assert!(!shards_map.is_empty());
        assert_eq!(shards_map.len(), 1);
        shards_map.update(2, |v| {
            assert_eq!(v, None);
            (UpdateAction::Keep, ())
        });
        shards_map.simple_update(&3, |v| {
            assert_eq!(v, None);
            (SimpleAction::Remove, ())
        });
        assert!(!shards_map.is_empty());
        assert_eq!(shards_map.len(), 1);
        shards_map.update(1, |v| {
            assert_eq!(v.cloned(), Some(1));
            (UpdateAction::Replace(2), ())
        });
        shards_map.update(1, |v| {
            assert_eq!(v.cloned(), Some(2));
            (UpdateAction::Keep, ())
        });
        shards_map.simple_update(&1, |v| {
            assert_eq!(v.cloned(), Some(2));
            (SimpleAction::Remove, ())
        });
        assert!(shards_map.is_empty());
        assert_eq!(shards_map.len(), 0);
        shards_map.simple_update(&1, |v| {
            assert_eq!(v, None);
            (SimpleAction::Remove, ())
        });
        assert!(shards_map.is_empty());
        assert_eq!(shards_map.len(), 0);
    }

    #[test]
    fn test_shards_map_2() {
        let shards_map = ShardsMap::<String, String>::with_capacity_and_shard_amount(256, 16);
        shards_map.update_by_ref("hello", |v| {
            assert_eq!(v, None);
            (UpdateAction::Replace("world".to_string()), ())
        });
        shards_map.update_by_ref("hello", |v| {
            assert_eq!(v.unwrap(), "world");
            (UpdateAction::Replace("lockmap".to_string()), ())
        });
        shards_map.simple_update("hello", |v| {
            assert_eq!(v, Some(&mut "lockmap".to_string()));
            (SimpleAction::Remove, ())
        });
        shards_map.simple_update("hello", |v| {
            assert_eq!(v, None);
            (SimpleAction::Remove, ())
        });
        shards_map.update_by_ref("hello", |v| {
            assert_eq!(v, None);
            (UpdateAction::Replace("lockmap".to_string()), ())
        });
        shards_map.simple_update("hello", |v| {
            assert_eq!(v.unwrap(), "lockmap");
            (SimpleAction::Remove, ())
        });
        shards_map.simple_update("hello", |v| {
            assert_eq!(v, None);
            (SimpleAction::Remove, ())
        });
        shards_map.update_by_ref("hello", |v| {
            assert_eq!(v, None);
            (UpdateAction::Keep, ())
        });
        shards_map.update_by_ref(&"hello".to_owned(), |v| {
            assert_eq!(v, None);
            (UpdateAction::Keep, ())
        });
        shards_map.simple_update("hello", |v| {
            assert_eq!(v, None);
            (SimpleAction::Keep, ())
        });
    }

    #[test]
    fn test_shards_map_concurrent() {
        let lock_map = Arc::new(ShardsMap::<u32, usize>::with_capacity_and_shard_amount(
            256, 16,
        ));
        let current = Arc::new(AtomicU32::default());
        const N: usize = 1 << 12;
        const M: usize = 8;

        lock_map.update(1, |_| (UpdateAction::Replace(0), ()));

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let current = current.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        lock_map.update(1, |v| {
                            let now = current.fetch_add(1, Ordering::AcqRel);
                            assert_eq!(now, 0);
                            *v.unwrap() += 1;
                            let now = current.fetch_sub(1, Ordering::AcqRel);
                            assert_eq!(now, 1);
                            (UpdateAction::Keep, ())
                        });
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(
            lock_map.update(1, |v| (UpdateAction::Replace(0), *v.unwrap())),
            N * M
        );
    }
}
