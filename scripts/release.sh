#!/bin/bash

# Release script for lockmap v0.1.14
# This script automates the release process

set -e

echo "🚀 Preparing release v0.1.14 for lockmap..."

# Verify we're on main branch
current_branch=$(git branch --show-current)
if [ "$current_branch" != "main" ]; then
    echo "❌ Error: Must be on main branch. Current branch: $current_branch"
    echo "Run: git checkout main && git pull origin main"
    exit 1
fi

# Verify version in Cargo.toml
version=$(grep -E '^version = ' Cargo.toml | sed 's/version = "\(.*\)"/\1/')
if [ "$version" != "0.1.14" ]; then
    echo "❌ Error: Version in Cargo.toml is $version, expected 0.1.14"
    exit 1
fi

echo "✅ Version check passed: $version"

# Run tests
echo "🧪 Running tests..."
cargo test
echo "✅ Tests passed"

# Run build
echo "🔨 Building project..."
cargo build
echo "✅ Build successful"

# Check if tag already exists
if git tag -l | grep -q "^v0.1.14$"; then
    echo "❌ Error: Tag v0.1.14 already exists"
    echo "To delete existing tag: git tag -d v0.1.14"
    exit 1
fi

# Create release tag
echo "📦 Creating release tag v0.1.14..."
git tag v0.1.14 -m "Release v0.1.14

## What's Changed

* Improve documentation comments throughout the project (#17)

**Full Changelog**: https://github.com/SF-Zhou/lockmap/compare/v0.1.13...v0.1.14"

echo "✅ Tag v0.1.14 created"

# Push tag
echo "🚀 Pushing tag to trigger release..."
git push origin v0.1.14

echo "✅ Release tag pushed successfully!"
echo ""
echo "🎉 Release process initiated!"
echo ""
echo "Monitor the release process:"
echo "  GitHub Actions: https://github.com/SF-Zhou/lockmap/actions"
echo "  GitHub Releases: https://github.com/SF-Zhou/lockmap/releases"
echo "  crates.io: https://crates.io/crates/lockmap"
echo ""
echo "The GitHub Actions workflow will automatically:"
echo "  1. Create GitHub release"
echo "  2. Publish to crates.io"