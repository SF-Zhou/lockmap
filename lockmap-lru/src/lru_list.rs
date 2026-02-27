use std::cell::UnsafeCell;
use std::ptr::NonNull;

/// An intrusive doubly-linked list node.
///
/// This structure is embedded directly into the State to form a per-shard LRU list.
/// Using an intrusive design avoids extra allocations and improves cache locality.
pub struct ListNode {
    prev: UnsafeCell<Option<NonNull<ListNode>>>,
    next: UnsafeCell<Option<NonNull<ListNode>>>,
}

impl ListNode {
    /// Creates a new unlinked list node.
    pub const fn new() -> Self {
        Self {
            prev: UnsafeCell::new(None),
            next: UnsafeCell::new(None),
        }
    }

    /// Returns true if this node is currently linked in a list.
    pub fn is_linked(&self) -> bool {
        // SAFETY: We're only reading, which is safe since we hold the shard lock
        unsafe { (*self.prev.get()).is_some() || (*self.next.get()).is_some() }
    }

    /// # Safety
    ///
    /// Must be called while holding the shard lock. The node must not be currently linked.
    pub unsafe fn unlink(&self) {
        let prev = (*self.prev.get()).take();
        let next = (*self.next.get()).take();

        if let Some(mut prev_ptr) = prev {
            *prev_ptr.as_mut().next.get() = next;
        }
        if let Some(mut next_ptr) = next {
            *next_ptr.as_mut().prev.get() = prev;
        }
    }
}

/// An intrusive LRU list head.
///
/// This maintains head and tail pointers for a doubly-linked list.
/// Most recently used items are at the head, least recently used at the tail.
pub struct LruList {
    head: UnsafeCell<Option<NonNull<ListNode>>>,
    tail: UnsafeCell<Option<NonNull<ListNode>>>,
    len: UnsafeCell<usize>,
}

// SAFETY: LruList is Sync because all access is protected by the shard lock
unsafe impl Sync for LruList {}
// SAFETY: LruList is Send because it doesn't contain non-Send types
unsafe impl Send for LruList {}

impl LruList {
    /// Creates a new empty LRU list.
    pub const fn new() -> Self {
        Self {
            head: UnsafeCell::new(None),
            tail: UnsafeCell::new(None),
            len: UnsafeCell::new(0),
        }
    }

    /// Returns the number of nodes in the list.
    ///
    /// # Safety
    ///
    /// Must be called while holding the shard lock.
    pub unsafe fn len(&self) -> usize {
        *self.len.get()
    }

    /// Moves a node to the head of the list (marks it as most recently used).
    ///
    /// # Safety
    ///
    /// Must be called while holding the shard lock.
    /// The node pointer must be valid and point to a node that's either already in this list
    /// or is unlinked.
    pub unsafe fn move_to_head(&self, node: NonNull<ListNode>) {
        let node_ref = node.as_ref();

        // Unlink if already in list
        if node_ref.is_linked() {
            // Use remove() to properly update head/tail pointers
            self.remove(node);
        }

        // Insert at head
        let old_head = (*self.head.get()).replace(node);
        *node.as_ref().prev.get() = None;
        *node.as_ref().next.get() = old_head;

        if let Some(mut old_head_ptr) = old_head {
            *old_head_ptr.as_mut().prev.get() = Some(node);
        } else {
            // List was empty, update tail
            *self.tail.get() = Some(node);
        }

        *self.len.get() += 1;
    }

    /// Removes and returns the tail node (least recently used).
    ///
    /// # Safety
    ///
    /// Must be called while holding the shard lock.
    pub unsafe fn pop_tail(&self) -> Option<NonNull<ListNode>> {
        let tail_ptr = (*self.tail.get())?;
        let tail_ref = tail_ptr.as_ref();

        // Save the prev before unlinking
        let prev = *tail_ref.prev.get();

        tail_ref.unlink();
        *self.len.get() -= 1;

        // Update tail pointer
        *self.tail.get() = prev;
        if let Some(new_tail) = prev {
            *new_tail.as_ref().next.get() = None;
        } else {
            // List is now empty
            *self.head.get() = None;
        }

        Some(tail_ptr)
    }

    /// Removes a specific node from the list.
    ///
    /// # Safety
    ///
    /// Must be called while holding the shard lock.
    /// The node must be in this list.
    pub unsafe fn remove(&self, node: NonNull<ListNode>) {
        let node_ref = node.as_ref();
        if !node_ref.is_linked() {
            return;
        }

        let prev = *node_ref.prev.get();
        let next = *node_ref.next.get();

        // Update head/tail if needed
        if (*self.head.get()) == Some(node) {
            *self.head.get() = next;
        }
        if (*self.tail.get()) == Some(node) {
            *self.tail.get() = prev;
        }

        node_ref.unlink();
        *self.len.get() -= 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[allow(dead_code)]
    struct TestNode {
        list_node: ListNode,
        value: i32,
    }

    impl TestNode {
        fn new(value: i32) -> Box<Self> {
            Box::new(Self {
                list_node: ListNode::new(),
                value,
            })
        }
    }

    #[test]
    fn test_lru_list_basic() {
        let list = LruList::new();

        let node1 = TestNode::new(1);
        let node2 = TestNode::new(2);
        let node3 = TestNode::new(3);

        let ptr1 = NonNull::from(&node1.list_node);
        let ptr2 = NonNull::from(&node2.list_node);
        let ptr3 = NonNull::from(&node3.list_node);

        unsafe {
            assert_eq!(list.len(), 0);

            // Add nodes
            list.move_to_head(ptr1);
            assert_eq!(list.len(), 1);

            list.move_to_head(ptr2);
            assert_eq!(list.len(), 2);

            list.move_to_head(ptr3);
            assert_eq!(list.len(), 3);

            // Pop from tail (should get node1)
            let popped = list.pop_tail();
            assert!(popped.is_some());
            assert_eq!(list.len(), 2);

            // Move node2 to head
            list.move_to_head(ptr2);
            assert_eq!(list.len(), 2);

            // Pop should now get node3
            let popped = list.pop_tail();
            assert!(popped.is_some());
            assert_eq!(list.len(), 1);

            // Final pop should get node2
            let popped = list.pop_tail();
            assert!(popped.is_some());
            assert_eq!(list.len(), 0);

            // List should be empty
            let popped = list.pop_tail();
            assert!(popped.is_none());
        }
    }

    #[test]
    fn test_lru_list_remove() {
        let list = LruList::new();

        let node1 = TestNode::new(1);
        let node2 = TestNode::new(2);
        let node3 = TestNode::new(3);

        let ptr1 = NonNull::from(&node1.list_node);
        let ptr2 = NonNull::from(&node2.list_node);
        let ptr3 = NonNull::from(&node3.list_node);

        unsafe {
            list.move_to_head(ptr1);
            list.move_to_head(ptr2);
            list.move_to_head(ptr3);
            assert_eq!(list.len(), 3);

            // Remove middle node
            list.remove(ptr2);
            assert_eq!(list.len(), 2);

            // Should pop node1 (tail)
            let popped = list.pop_tail();
            assert!(popped.is_some());
            assert_eq!(list.len(), 1);

            // Should pop node3 (now the only one left)
            let popped = list.pop_tail();
            assert!(popped.is_some());
            assert_eq!(list.len(), 0);
        }
    }
}
