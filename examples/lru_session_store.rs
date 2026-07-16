//! Bounded session store built on `LruLockMap`.
//!
//! - Capacity-bounded: the least recently used session is evicted
//!   automatically when the store is full.
//! - `peek` inspects a session without marking it as recently used.
//! - `pop_lru` explicitly reclaims the coldest session.
//! - Sessions held by an entry guard are never evicted, even at capacity.
//!
//! Run with: `cargo run --example lru_session_store`

use lockmap::LruLockMap;

#[derive(Clone, Debug)]
struct Session {
    user: String,
    hits: u32,
}

fn main() {
    // A tiny single-shard store so the eviction order is easy to follow.
    let sessions = LruLockMap::<u64, Session>::with_options(3, 3, 1);

    for id in 1..=3u64 {
        sessions.insert(
            id,
            Session {
                user: format!("user-{id}"),
                hits: 0,
            },
        );
    }

    // Touch session 1 through the entry API: this promotes it to
    // most-recently-used and updates it atomically.
    {
        let mut entry = sessions.entry(1);
        if let Some(session) = entry.get_mut() {
            session.hits += 1;
        }
    }

    // Inserting a 4th session evicts the LRU one. Session 2 is now the
    // coldest (session 1 was just promoted), so it is the one that goes.
    sessions.insert(
        4,
        Session {
            user: "user-4".into(),
            hits: 0,
        },
    );
    assert!(sessions.peek(&2).is_none(), "session 2 was evicted");
    assert!(sessions.peek(&1).is_some(), "session 1 survived (promoted)");

    // `peek` does not disturb the LRU order, so it is safe for monitoring.
    for id in [1u64, 3, 4] {
        if let Some(session) = sessions.peek(&id) {
            println!("session {id}: {session:?}");
        }
    }

    // Explicitly drain the coldest sessions, e.g. on memory pressure.
    while let Some((id, session)) = sessions.pop_lru() {
        println!("reclaimed session {id} of {}", session.user);
    }
    assert!(sessions.is_empty());
}
