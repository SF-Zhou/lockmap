# Release Instructions for v0.1.14

This document provides step-by-step instructions to create release v0.1.14 for the lockmap project.

## Prerequisites

- Push access to the main repository
- All changes merged to main branch
- Version already updated to 0.1.14 in Cargo.toml ✅

## Release Process

### 1. Verify Current State

```bash
# Ensure you're on the main branch with latest changes
git checkout main
git pull origin main

# Verify tests pass
cargo test

# Verify build succeeds  
cargo build

# Check current version
grep version Cargo.toml
# Should show: version = "0.1.14"
```

### 2. Create and Push Release Tag

```bash
# Create annotated tag with release notes
git tag v0.1.14 -m "Release v0.1.14

## What's Changed

* Improve documentation comments throughout the project (#17)

**Full Changelog**: https://github.com/SF-Zhou/lockmap/compare/v0.1.13...v0.1.14"

# Push the tag to trigger GitHub Actions release workflow
git push origin v0.1.14
```

### 3. Automated Actions

Once the tag is pushed, GitHub Actions will automatically:

1. **Create GitHub Release**: The release.yml workflow will trigger and create a GitHub release
2. **Publish to crates.io**: The workflow will automatically publish the new version to crates.io using the authenticated token

### 4. Verify Release

After pushing the tag, verify:

1. **GitHub Release**: Check https://github.com/SF-Zhou/lockmap/releases for the new v0.1.14 release
2. **crates.io**: Check https://crates.io/crates/lockmap for the updated version
3. **CI Status**: Monitor the GitHub Actions workflow at https://github.com/SF-Zhou/lockmap/actions

## Release Notes

### Changes in v0.1.14

- **Documentation**: Improve documentation comments throughout the project (#17)
  - Enhanced inline documentation for better developer experience
  - Improved code examples and usage instructions
  - Better formatted docstrings across all modules

### Previous Release
- **v0.1.13**: Support batch lock functionality

## Rollback Plan

If issues are discovered after release:

1. **GitHub Release**: Mark as pre-release or delete if necessary
2. **crates.io**: Use `cargo yank` to remove the problematic version
3. **Hotfix**: Create hotfix branch, fix issues, and release new patch version

## Notes

- The GitHub Actions workflow is already configured in `.github/workflows/release.yml`
- The workflow requires the `release` environment with appropriate secrets
- crates.io authentication is handled via the `rust-lang/crates-io-auth-action`