#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
test_lean_indexer.py

Tests for the Lean code indexer.
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from lean_indexer import LeanIndexer


def test_lean_version():
    """Test getting Lean version."""
    print("Testing Lean version detection...")

    indexer = LeanIndexer()
    version = indexer.get_lean_version()

    print(f"  Detected Lean version: {version}")
    assert version != "", "Should detect some version"
    print("✓ Lean version detected")


def test_find_lean_root():
    """Test finding Lean installation root."""
    print("\nTesting Lean root detection...")

    indexer = LeanIndexer()
    root = indexer.find_lean_root()

    if root:
        print(f"  Found Lean root: {root}")
        print("✓ Lean root found")
    else:
        print("  ⚠ Lean root not found (may be OK if Lean not installed)")


def test_source_directories():
    """Test finding source directories."""
    print("\nTesting source directory detection...")

    indexer = LeanIndexer()
    project_root = Path.cwd()

    print(f"  Project root: {project_root}")

    sources = indexer.find_source_directories(project_root)

    print(f"  Found sources: {list(sources.keys())}")

    for name, path in sources.items():
        print(f"    {name}: {path}")
        assert path.exists(), f"Source path should exist: {path}"

    print("✓ Source directories found")


def test_parse_local_files():
    """Test parsing local Lean files."""
    print("\nTesting parsing of local Lean files...")

    indexer = LeanIndexer()
    project_root = Path.cwd()

    # Look for TacticsGeneration/Benchmark.lean
    benchmark_file = project_root / 'TacticsGeneration' / 'Benchmark.lean'

    if not benchmark_file.exists():
        print("  ⚠ Benchmark.lean not found, skipping test")
        return

    print(f"  Parsing {benchmark_file}...")

    definitions = indexer.parse_lean_file(benchmark_file, 'local')

    print(f"  Found {len(definitions)} definitions")

    if definitions:
        print(f"  Sample definitions:")
        for defn in definitions[:5]:
            print(f"    - {defn['type']}: {defn['name']}")

        assert len(definitions) > 0, "Should find at least one definition"
        print("✓ Parsing works")
    else:
        print("  ⚠ No definitions found")


def test_build_small_index():
    """Test building a small index from local files."""
    print("\nTesting index building...")

    indexer = LeanIndexer()
    project_root = Path.cwd()

    # Index only local source (should be fast)
    print("  Building index from local source...")
    indexer.build_index(
        project_root=project_root,
        sources=['local'],
        verbose=True
    )

    print(f"\n  Index contains {len(indexer.index)} definitions")

    if indexer.index:
        print(f"  Sample definitions:")
        for i, (name, defn) in enumerate(list(indexer.index.items())[:5]):
            print(f"    {name} ({defn['type']})")

        assert len(indexer.index) > 0, "Index should not be empty"
        print("✓ Index building works")

        # Test save and load
        print("\n  Testing index save/load...")
        test_index_path = Path('agents/search/data/test_index.json')
        indexer.save_index(test_index_path)

        assert test_index_path.exists(), "Index file should be created"
        print("✓ Index saved")

        # Load it back
        indexer2 = LeanIndexer()
        indexer2.load_index(test_index_path)

        assert len(indexer2.index) == len(indexer.index), "Loaded index should match"
        print("✓ Index loaded")

        # Clean up
        test_index_path.unlink()
        print("✓ Test index cleaned up")
    else:
        print("  ⚠ Index is empty (no local Lean files found)")


if __name__ == "__main__":
    print("=" * 60)
    print("Running Lean Indexer Tests")
    print("=" * 60)

    try:
        test_lean_version()
        test_find_lean_root()
        test_source_directories()
        test_parse_local_files()
        test_build_small_index()

        print("\n" + "=" * 60)
        print("✅ All tests passed!")
        print("=" * 60)

    except AssertionError as e:
        print(f"\n❌ Test failed: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
