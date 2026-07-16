# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Add non-blocking `try_entry` / `try_entry_by_ref` to `LockMap` and `LruLockMap`
- Add `clear` to `LockMap` and `LruLockMap`
- Add `peek` to `LruLockMap`: read a value without promoting it in the LRU list
- Add `pop_lru` to `LruLockMap`: remove and return a least-recently-used entry
  (per shard, round-robin across shards; in-use entries are skipped)
- Expand benchmarks with multi-threaded workloads: concurrent get, mixed
  get/insert, hot-key entry contention, LRU `get` vs `peek`, and mixed workload
  under eviction pressure

### Changed

- Use `parking_lot::Mutex` for internal shard locks. This removes lock poisoning:
  previously, a panic inside `V::clone()` during `get()` poisoned the shard and made
  all subsequent operations on that shard panic
- Check reference-count overflow with `debug_assert` in debug builds

### Internal

- Deduplicate shared internals (`StateFlags`, shard sizing, guard release logic)
- Attach README doctests via the `#[cfg(doctest)]` idiom instead of a private module
- Declare `rust-version` (MSRV 1.75) and crates.io `keywords` / `categories` metadata
- Pin dev-dependency versions (`criterion = "0.8"`, `rand = "0.10"`)

### CI

- Run Miri on the whole library test suite (`cargo miri test --lib`)
- Add a lint job enforcing `cargo fmt --check` and `cargo clippy -- -D warnings`

## [0.2.2] - 2026-04-27

### Added

- Add `max_evict` parameter to `try_evict` to limit the number of evictions per call (#35)

## [0.2.1] - 2026-03-10

### Fixed

- Remove `Send` bound from `Entry`/`LruEntry` and relax `Sync` bounds for correctness (#34)

### CI

- Enhance CI workflow with multi-OS and multi-architecture build matrix (#32)
- Upgrade `codecov-action` (#31)

### Documentation

- Add Crates.io download-count badge to README (#33)

## [0.2.0] - 2026-03-05

### Changed

- **Breaking:** Consolidate workspace into a single crate; migrate to `parking_lot` mutex and `HashTable`-based `LockMap` with a unified `Entry` API (#30)

  Migration guide:

  | 0.1.x | 0.2.0 |
  |-------|-------|
  | `use lockmap::EntryByVal` | `use lockmap::Entry` |
  | `use lockmap::EntryByRef` | `use lockmap::Entry` |
  | `use lockmap_lru::LruLockMap` | `use lockmap::LruLockMap` |
  | `use lockmap_lru::LruEntry` | `use lockmap::LruEntry` |

### Added

- Add `set_max_size` interface for LRU cache size control (#29)

### Performance

- Single-hash, single-probe optimizations for LRU cache using the entry API (#27)

## [0.1.16] - 2025-12-30

### Performance

- Further optimize entry cleanup to reduce overhead (#25)

## [0.1.15] - 2025-12-28

### Fixed

- Fix Miri violations and improve concurrency safety (#22)

### Performance

- Optimize entry cleanup (#24)

### CI

- Speed up CI pipeline (#19)

### Documentation

- Add FAQ section addressing Miri test failure scenarios (#21)

## [0.1.14] - 2025-09-04

### Fixed

- Fix elided lifetime compilation warning (#15)

### Documentation

- Improve documentation comments throughout the project (#17)

## [0.1.13] - 2025-08-01

### Added

- Support batch lock acquisition for multiple keys atomically (#14)

## [0.1.12] - 2025-07-25

### Added

- Initial release of `lockmap` with a thread-safe, fine-grained per-key locking `HashMap`
- Use `foldhash` as the default hasher for improved performance (#10)
- Add benchmarks (#10)
- Add MIT and Apache-2.0 dual-license headers (#9)
- Configure trusted publishing via `crates.io` (#13)

### Changed

- Iterative interface optimizations across multiple releases (#3, #4, #6, #7)
- Performance improvements to the core locking implementation (#5)

[0.2.2]: https://github.com/SF-Zhou/lockmap/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/SF-Zhou/lockmap/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/SF-Zhou/lockmap/compare/v0.1.16...v0.2.0
[0.1.16]: https://github.com/SF-Zhou/lockmap/compare/v0.1.15...v0.1.16
[0.1.15]: https://github.com/SF-Zhou/lockmap/compare/v0.1.14...v0.1.15
[0.1.14]: https://github.com/SF-Zhou/lockmap/compare/v0.1.13...v0.1.14
[0.1.13]: https://github.com/SF-Zhou/lockmap/compare/v0.1.12...v0.1.13
[0.1.12]: https://github.com/SF-Zhou/lockmap/releases/tag/v0.1.12
