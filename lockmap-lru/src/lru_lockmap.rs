//! Simplified LRU implementation - basic get/insert/remove operations
//!
//! This is a simplified implementation that demonstrates LRU eviction.
//! The full entry() API can be added in a future iteration.

use crate::lru_list::{ListNode, LruList};
use aliasable::boxed::AliasableBox;
use std::borrow::Borrow;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;
use std::sync::{Mutex as StdMutex, OnceLock};

use foldhash::fast::RandomState;
use std::hash::BuildHasher;

/// Internal state for an LRU entry.
struct LruState<V> {
    value: UnsafeCell<Option<V>>,
    list_node: ListNode,
}

impl<V> LruState<V> {
    fn new(value: Option<V>) -> AliasableBox<Self> {
        AliasableBox::from_unique(Box::new(Self {
            value: UnsafeCell::new(value),
            list_node: ListNode::new(),
        }))
    }

    unsafe fn value_ref(&self) -> &Option<V> {
        &*self.value.get()
    }

    unsafe fn value_mut(&self) -> &mut Option<V> {
        &mut *self.value.get()
    }

    fn list_node_ptr(&self) -> NonNull<ListNode> {
        NonNull::from(&self.list_node)
    }
}

/// A sharded LRU-enabled map.
struct LruShardMap<K, V> {
    map: StdMutex<HashMap<K, AliasableBox<LruState<V>>, RandomState>>,
    lru_list: LruList,
    capacity: usize,
}

// SAFETY: LruShardMap is Sync because access to lru_list is protected by the map mutex
unsafe impl<K: Send, V: Send> Sync for LruShardMap<K, V> {}
// SAFETY: LruShardMap is Send because all fields are Send
unsafe impl<K: Send, V: Send> Send for LruShardMap<K, V> {}

impl<K, V> LruShardMap<K, V>
where
    K: Eq + Hash + Clone,
{
    fn with_capacity(capacity: usize) -> Self {
        Self {
            map: StdMutex::new(HashMap::with_capacity_and_hasher(
                capacity,
                RandomState::default(),
            )),
            lru_list: LruList::new(),
            capacity,
        }
    }

    fn len(&self) -> usize {
        self.map.lock().unwrap().len()
    }

    fn is_empty(&self) -> bool {
        self.map.lock().unwrap().is_empty()
    }

    unsafe fn evict_if_needed(&self, map: &mut HashMap<K, AliasableBox<LruState<V>>, RandomState>) {
        while self.lru_list.len() > self.capacity {
            if let Some(tail_node) = self.lru_list.pop_tail() {
                // Get state pointer from list node
                let state_ptr = (tail_node.as_ptr() as *const u8)
                    .sub(offset_of!(LruState<V>, list_node))
                    as *const LruState<V>;

                // Find and remove from map
                let mut to_remove: Option<K> = None;
                for (key, value) in map.iter() {
                    let v_ptr = &**value as *const LruState<V>;
                    if v_ptr == state_ptr {
                        to_remove = Some(key.clone());
                        break;
                    }
                }
                if let Some(key) = to_remove {
                    map.remove(&key);
                }
            } else {
                break;
            }
        }
    }

    fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        let map = self.map.lock().unwrap();
        if let Some(state) = map.get(key) {
            unsafe {
                self.lru_list.move_to_head(state.list_node_ptr());
                state.value_ref().clone()
            }
        } else {
            None
        }
    }

    fn insert(&self, key: K, value: V) -> Option<V> {
        let mut map = self.map.lock().unwrap();

        if let Some(state) = map.get(&key) {
            unsafe {
                self.lru_list.move_to_head(state.list_node_ptr());
                state.value_mut().replace(value)
            }
        } else {
            let state = LruState::new(Some(value));
            unsafe {
                self.lru_list.move_to_head(state.list_node_ptr());
            }
            map.insert(key, state);
            unsafe {
                self.evict_if_needed(&mut map);
            }
            None
        }
    }

    fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let map = self.map.lock().unwrap();
        if let Some(state) = map.get(key) {
            unsafe {
                self.lru_list.move_to_head(state.list_node_ptr());
                state.value_ref().is_some()
            }
        } else {
            false
        }
    }

    fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let mut map = self.map.lock().unwrap();
        if let Some((_, state)) = map.remove_entry(key) {
            unsafe {
                self.lru_list.remove(state.list_node_ptr());
                state.value_mut().take()
            }
        } else {
            None
        }
    }
}

/// A sharded collection of LRU maps.
struct LruShardsMap<K, V> {
    shards: Vec<LruShardMap<K, V>>,
    hasher: RandomState,
}

impl<K, V> LruShardsMap<K, V>
where
    K: Eq + Hash + Clone,
{
    fn with_capacity_and_shard_amount(capacity_per_shard: usize, shard_amount: usize) -> Self {
        Self {
            shards: (0..shard_amount)
                .map(|_| LruShardMap::with_capacity(capacity_per_shard))
                .collect(),
            hasher: RandomState::default(),
        }
    }

    fn len(&self) -> usize {
        self.shards.iter().map(|s| s.len()).sum()
    }

    fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| s.is_empty())
    }

    #[inline(always)]
    fn shard<Q>(&self, key: &Q) -> &LruShardMap<K, V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        let idx = self.hasher.hash_one(key) as usize % self.shards.len();
        &self.shards[idx]
    }
}

fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}

/// An LRU-enabled thread-safe hashmap with automatic eviction.
///
/// This provides a simplified LRU cache with per-shard capacity limits.
/// When a shard exceeds capacity, the least recently used entries are evicted.
///
/// # Examples
///
/// ```
/// use lockmap_lru::LruLockMap;
///
/// let map = LruLockMap::<String, u32>::with_capacity_per_shard(100);
/// map.insert("key".into(), 42);
/// assert_eq!(map.get("key"), Some(42));
/// ```
pub struct LruLockMap<K, V> {
    map: LruShardsMap<K, V>,
}

impl<K: Eq + Hash + Clone, V> Default for LruLockMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash + Clone, V> LruLockMap<K, V> {
    /// Creates a new LRU map with default capacity (1000 per shard).
    pub fn new() -> Self {
        Self::with_capacity_per_shard(1000)
    }

    /// Creates a new LRU map with specified capacity per shard.
    pub fn with_capacity_per_shard(capacity_per_shard: usize) -> Self {
        Self {
            map: LruShardsMap::with_capacity_and_shard_amount(
                capacity_per_shard,
                default_shard_amount(),
            ),
        }
    }

    /// Creates a new LRU map with specified capacity and shard amount.
    pub fn with_capacity_and_shard_amount(capacity_per_shard: usize, shard_amount: usize) -> Self {
        Self {
            map: LruShardsMap::with_capacity_and_shard_amount(capacity_per_shard, shard_amount),
        }
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the map is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Gets a value from the map.
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
        Q: Eq + Hash + ?Sized,
    {
        self.map.shard(key).get(key)
    }

    /// Inserts a value into the map.
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        self.map.shard(&key).insert(key, value)
    }

    /// Checks if the map contains a key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.shard(key).contains_key(key)
    }

    /// Removes a key from the map.
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.shard(key).remove(key)
    }
}

impl<K, V> std::fmt::Debug for LruLockMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LruLockMap").finish()
    }
}

macro_rules! offset_of {
    ($type:ty, $field:tt) => {{
        let dummy = std::mem::MaybeUninit::<$type>::uninit();
        let dummy_ptr = dummy.as_ptr();
        let field_ptr = unsafe { std::ptr::addr_of!((*dummy_ptr).$field) };
        (field_ptr as usize) - (dummy_ptr as usize)
    }};
}

use offset_of;
