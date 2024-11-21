use std::borrow::Borrow;
use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::Mutex;

/// Represents the action to be taken on a value in the `ShardMap`.
pub enum Action<V> {
    /// Keep the current value unchanged.
    Keep,
    /// Remove the value from the map.
    Remove,
    /// Update the value with the provided new value.
    Update(V),
}

/// A thread-safe hashmap shard.
///
/// This struct wraps a `HashMap` protected by a `Mutex` to ensure thread safety.
#[derive(Debug)]
pub struct ShardMap<K, V> {
    /// The underlying hashmap protected by a `Mutex`.
    map: Mutex<HashMap<K, V>>,
}

impl<K, V> ShardMap<K, V>
where
    K: Eq + Hash + Clone,
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
            map: Mutex::new(HashMap::with_capacity(capacity)),
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
    pub fn update<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized + ToOwned<Owned = K>,
        F: FnOnce(Option<&mut V>) -> (Action<V>, R),
    {
        let mut map = self.map.lock().unwrap();
        match map.get_mut(key) {
            Some(value) => {
                let (action, ret) = func(Some(value));
                match action {
                    Action::Keep => {}
                    Action::Remove => {
                        map.remove(key);
                    }
                    Action::Update(value) => {
                        map.insert(key.to_owned(), value);
                    }
                }
                ret
            }
            None => {
                let (action, ret) = func(None);
                match action {
                    Action::Keep => {}
                    Action::Remove => {}
                    Action::Update(value) => {
                        map.insert(key.to_owned(), value);
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
    K: Eq + Hash + Clone,
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
    pub fn update<Q, F, R>(&self, key: &Q, func: F) -> R
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized + ToOwned<Owned = K>,
        F: FnOnce(Option<&mut V>) -> (Action<V>, R),
    {
        let mut s = DefaultHasher::new();
        key.hash(&mut s);
        let idx = s.finish() as usize % self.shards.len();
        self.shards[idx].update(key, func)
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
        shards_map.update(&1, |v| {
            assert_eq!(v, None);
            (Action::Update(1), ())
        });
        shards_map.update(&2, |v| {
            assert_eq!(v, None);
            (Action::Keep, ())
        });
        shards_map.update(&3, |v| {
            assert_eq!(v, None);
            (Action::Remove, ())
        });
        shards_map.update(&1, |v| {
            assert_eq!(v.cloned(), Some(1));
            (Action::Update(2), ())
        });
        shards_map.update(&1, |v| {
            assert_eq!(v.cloned(), Some(2));
            (Action::Keep, ())
        });
        shards_map.update(&1, |v| {
            assert_eq!(v.cloned(), Some(2));
            (Action::Remove, ())
        });
        shards_map.update(&1, |v| {
            assert_eq!(v, None);
            (Action::Remove, ())
        });
    }

    #[test]
    fn test_shards_map_2() {
        let shards_map = ShardsMap::<String, String>::with_capacity_and_shard_amount(256, 16);
        shards_map.update("hello", |v| {
            assert_eq!(v, None);
            (Action::Update("world".to_string()), ())
        });
        shards_map.update("hello", |v| {
            assert_eq!(v.cloned(), Some("world".into()));
            (Action::Remove, ())
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

        lock_map.update(&1, |_| (Action::Update(0), ()));

        let threads = (0..M)
            .map(|_| {
                let lock_map = lock_map.clone();
                let current = current.clone();
                std::thread::spawn(move || {
                    for _ in 0..N {
                        lock_map.update(&1, |v| {
                            let now = current.fetch_add(1, Ordering::AcqRel);
                            assert_eq!(now, 0);
                            *v.unwrap() += 1;
                            let now = current.fetch_sub(1, Ordering::AcqRel);
                            assert_eq!(now, 1);
                            (Action::Keep, ())
                        });
                    }
                })
            })
            .collect::<Vec<_>>();
        threads.into_iter().for_each(|t| t.join().unwrap());

        assert_eq!(
            lock_map.update(&1, |v| (Action::Update(0), *v.unwrap())),
            N * M
        );
    }
}
