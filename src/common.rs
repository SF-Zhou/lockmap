//! Internal helpers shared by [`LockMap`](crate::LockMap) and
//! [`LruLockMap`](crate::LruLockMap).

use std::sync::OnceLock;

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

/// Default number of shards: `4 * available_parallelism`, rounded up to the
/// next power of two. Computed once and cached.
pub(crate) fn default_shard_amount() -> usize {
    static DEFAULT_SHARD_AMOUNT: OnceLock<usize> = OnceLock::new();
    *DEFAULT_SHARD_AMOUNT.get_or_init(|| {
        (std::thread::available_parallelism().map_or(1, usize::from) * 4).next_power_of_two()
    })
}
