//! Internal helpers shared by [`LockMap`](crate::LockMap) and
//! [`LruLockMap`](crate::LruLockMap).

use aliasable::boxed::AliasableBox;
use parking_lot::lock_api::RawMutex as _;
use parking_lot::RawMutex;
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::OnceLock;

// ---------------------------------------------------------------------------
// StateFlags
// ---------------------------------------------------------------------------

/// Packed per-key state: the highest bit records whether the entry currently
/// holds a value, the remaining 31 bits hold the guard reference count.
pub(crate) struct StateFlags(pub(crate) u32);

impl StateFlags {
    pub(crate) const HAS_VALUE_FLAG: u32 = 1 << 31;
    pub(crate) const REFCNT_MASK: u32 = !Self::HAS_VALUE_FLAG;

    pub(crate) fn new(refcnt: u32, has_value: bool) -> Self {
        let mut val = refcnt & Self::REFCNT_MASK;
        if has_value {
            val |= Self::HAS_VALUE_FLAG;
        }
        Self(val)
    }

    pub(crate) fn refcnt(&self) -> u32 {
        self.0 & Self::REFCNT_MASK
    }

    pub(crate) fn has_value(&self) -> bool {
        (self.0 & Self::HAS_VALUE_FLAG) != 0
    }

    pub(crate) fn pending_cleanup(&self) -> bool {
        self.0 == 0
    }
}

// ---------------------------------------------------------------------------
// State – per-key state with key, pre-computed hash and extra link payload
// ---------------------------------------------------------------------------

/// Per-key entry state shared by both map implementations.
///
/// `L` carries additional per-entry payload: `()` for `LockMap`, and the
/// intrusive LRU list pointers for `LruLockMap`.
pub(crate) struct State<K, V, L> {
    pub(crate) key: K,
    pub(crate) hash: u64,
    pub(crate) flags: AtomicU32,
    pub(crate) mutex: RawMutex,
    pub(crate) value: UnsafeCell<Option<V>>,
    pub(crate) links: L,
}

impl<K, V, L: Default> State<K, V, L> {
    pub(crate) fn new(key: K, value: Option<V>, refcnt: u32, hash: u64) -> AliasableBox<Self> {
        AliasableBox::from_unique(Box::new(Self {
            key,
            hash,
            flags: AtomicU32::new(StateFlags::new(refcnt, value.is_some()).0),
            mutex: RawMutex::INIT,
            value: UnsafeCell::new(value),
            links: L::default(),
        }))
    }
}

impl<K, V, L> State<K, V, L> {
    pub(crate) fn flags(&self) -> StateFlags {
        StateFlags(self.flags.load(Ordering::Acquire))
    }

    /// Increments the reference count.
    ///
    /// # Note
    ///
    /// The reference count uses 31 bits, supporting up to 2^31 - 1 concurrent
    /// references. Overflow is checked in debug builds only.
    pub(crate) fn inc_ref(&self) -> StateFlags {
        let old = self.flags.fetch_add(1, Ordering::AcqRel);
        debug_assert!(
            StateFlags(old).refcnt() < StateFlags::REFCNT_MASK,
            "lockmap: reference count overflow"
        );
        StateFlags(old + 1)
    }

    pub(crate) fn dec_ref(&self) -> StateFlags {
        StateFlags(self.flags.fetch_sub(1, Ordering::AcqRel) - 1)
    }

    pub(crate) fn set_value_state(&self, has_value: bool) {
        if has_value {
            self.flags
                .fetch_or(StateFlags::HAS_VALUE_FLAG, Ordering::Release);
        } else {
            self.flags
                .fetch_and(!StateFlags::HAS_VALUE_FLAG, Ordering::Release);
        }
    }

    /// # Safety
    ///
    /// The caller must ensure that the internal `mutex` is locked.
    pub(crate) unsafe fn value_ref(&self) -> &Option<V> {
        &*self.value.get()
    }

    /// # Safety
    ///
    /// The caller must ensure that the internal `mutex` is locked and they have exclusive access.
    #[allow(clippy::mut_from_ref)]
    pub(crate) unsafe fn value_mut(&self) -> &mut Option<V> {
        &mut *self.value.get()
    }

    /// Fast path of the reference-release protocol.
    ///
    /// Decrements the reference count with a CAS loop and returns `false` if
    /// nothing else needs to be done. Returns `true` **without decrementing**
    /// if this is the last reference and the entry holds no value; the caller
    /// must then acquire the shard lock, call [`dec_ref`](Self::dec_ref), and
    /// remove the entry from the shard if
    /// [`pending_cleanup`](StateFlags::pending_cleanup) is set.
    pub(crate) fn release_ref_needs_cleanup(&self) -> bool {
        let mut current = self.flags.load(Ordering::Acquire);
        loop {
            let flags = StateFlags(current);

            // If this is the last reference and no value, proceed to cleanup.
            if flags.refcnt() == 1 && !flags.has_value() {
                return true;
            }

            let new_flags = StateFlags::new(flags.refcnt() - 1, flags.has_value());
            match self.flags.compare_exchange_weak(
                current,
                new_flags.0,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return false, // Not the last reference or still has value.
                Err(actual) => current = actual,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Shard sizing
// ---------------------------------------------------------------------------

/// Default number of shards: `4 * available_parallelism`, rounded up to the
/// next power of two. Computed once and cached.
pub(crate) fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}
