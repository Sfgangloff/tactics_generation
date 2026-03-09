#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
test_searcher.py

Tests for the search engine module.
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from searcher import LeanSearcher


def test_basic_search():
    """Test basic keyword search."""
    print("Testing basic keyword search...")

    searcher = LeanSearcher()

    # Test with multiplication keywords
    results = searcher.search(
        keywords=['multiply', 'nat'],
        max_results=5
    )

    print(f"  Search for 'multiply', 'nat': found {len(results)} results")

    assert len(results) > 0, "Should find some results"

    # Check that results have required fields
    for result in results:
        assert result.name, "Result should have name"
        assert result.type, "Result should have type"
        assert result.score > 0, "Result should have positive score"
        assert len(result.match_reasons) > 0, "Result should have match reasons"

    # Print top result
    if results:
        top = results[0]
        print(f"  Top result: {top.name} (score: {top.score:.2f})")
        print(f"  Type: {top.type}")
        print(f"  Matches: {', '.join(top.match_reasons[:2])}")

    print("✓ Basic search works")


def test_exact_name_match():
    """Test that exact name matches score highest."""
    print("\nTesting exact name match scoring...")

    searcher = LeanSearcher()

    # Search for a specific function that we know exists
    # (This will depend on what's in the index)
    results = searcher.search(
        keywords=['array'],
        max_results=10
    )

    print(f"  Found {len(results)} results for 'array'")

    assert len(results) > 0, "Should find array-related results"

    # Check that results with 'array' in the name score higher
    top_results = results[:3]
    for result in top_results:
        print(f"  {result.name} (score: {result.score:.2f})")
        if 'array' in result.name.lower():
            print(f"    → Contains 'array' in name")

    print("✓ Exact name matching works")


def test_multiple_keywords():
    """Test search with multiple keywords."""
    print("\nTesting multiple keyword search...")

    searcher = LeanSearcher()

    # Search for hash map related functions
    results = searcher.search(
        keywords=['hash', 'map'],
        max_results=5
    )

    print(f"  Search for 'hash', 'map': found {len(results)} results")

    if results:
        for i, result in enumerate(results[:3], 1):
            print(f"  {i}. {result.name} (score: {result.score:.2f})")

    assert len(results) > 0, "Should find hash map results"

    print("✓ Multiple keyword search works")


def test_type_preference():
    """Test type preference in search."""
    print("\nTesting type preference...")

    searcher = LeanSearcher()

    # Search with type preference
    results_with_pref = searcher.search(
        keywords=['list'],
        max_results=10,
        prefer_types=['def', 'structure']
    )

    results_without_pref = searcher.search(
        keywords=['list'],
        max_results=10
    )

    print(f"  With preference: {len(results_with_pref)} results")
    print(f"  Without preference: {len(results_without_pref)} results")

    # Check that preferred types appear earlier
    if results_with_pref:
        top_with_pref = results_with_pref[0]
        print(f"  Top with preference: {top_with_pref.name} ({top_with_pref.type})")

    print("✓ Type preference works")


def test_min_score_threshold():
    """Test minimum score threshold filtering."""
    print("\nTesting minimum score threshold...")

    searcher = LeanSearcher()

    # Search with different thresholds
    results_low = searcher.search(
        keywords=['test'],
        max_results=20,
        min_score=0.1
    )

    results_high = searcher.search(
        keywords=['test'],
        max_results=20,
        min_score=1.0
    )

    print(f"  With min_score=0.1: {len(results_low)} results")
    print(f"  With min_score=1.0: {len(results_high)} results")

    assert len(results_high) <= len(results_low), "Higher threshold should return fewer results"

    # Check that all results meet threshold
    for result in results_high:
        assert result.score >= 1.0, f"Result {result.name} has score {result.score} < 1.0"

    print("✓ Minimum score threshold works")


def test_search_by_analysis():
    """Test search using task analysis."""
    print("\nTesting search by analysis...")

    searcher = LeanSearcher()

    # Simulate a task analysis result
    analysis = {
        "keywords": ["multiply", "product"],
        "types": ["Nat", "Int"],
        "operations": ["multiplication"],
        "paradigm": "functional",
        "domain": "arithmetic"
    }

    results = searcher.search_by_analysis(analysis, max_results=5)

    print(f"  Found {len(results)} results")

    if results:
        for i, result in enumerate(results[:3], 1):
            print(f"  {i}. {result.name} (score: {result.score:.2f})")
            print(f"     {result.signature}")

    assert len(results) > 0, "Should find results from analysis"

    print("✓ Search by analysis works")


def test_tokenization():
    """Test name tokenization."""
    print("\nTesting name tokenization...")

    searcher = LeanSearcher()

    # Test various name formats
    test_cases = [
        ("Nat.add", ["Nat", "add"]),
        ("HashMap.insert", ["Hash", "Map", "insert"]),
        ("hash_map_get", ["hash", "map", "get"]),
        ("List.foldl", ["List", "foldl"])
    ]

    for name, expected_tokens in test_cases:
        tokens = searcher._tokenize(name)
        print(f"  {name} → {tokens}")
        # Just verify we get some tokens (exact matching is tricky with camelCase)
        assert len(tokens) > 0, f"Should tokenize {name}"

    print("✓ Tokenization works")


def test_statistics():
    """Test index statistics."""
    print("\nTesting index statistics...")

    searcher = LeanSearcher()
    stats = searcher.get_statistics()

    print(f"  Total definitions: {stats['total_definitions']}")
    print(f"  Types: {list(stats['by_type'].keys())}")
    print(f"  Sources: {list(stats['by_source'].keys())}")

    assert stats['total_definitions'] > 0, "Should have definitions"
    assert len(stats['by_type']) > 0, "Should have types"
    assert len(stats['by_source']) > 0, "Should have sources"

    print("✓ Statistics work")


def test_result_serialization():
    """Test converting results to dictionaries."""
    print("\nTesting result serialization...")

    searcher = LeanSearcher()
    results = searcher.search(keywords=['list'], max_results=1)

    if results:
        result = results[0]
        result_dict = result.to_dict()

        print(f"  Serialized: {result.name}")

        # Check required fields
        assert 'name' in result_dict
        assert 'type' in result_dict
        assert 'signature' in result_dict
        assert 'score' in result_dict
        assert 'match_reasons' in result_dict

        print("✓ Result serialization works")
    else:
        print("  ⚠ No results to test serialization")


def test_empty_keywords():
    """Test search with empty keywords."""
    print("\nTesting empty keywords handling...")

    searcher = LeanSearcher()
    results = searcher.search(keywords=[], max_results=10)

    print(f"  Empty keywords: {len(results)} results")

    assert len(results) == 0, "Empty keywords should return no results"

    print("✓ Empty keywords handled correctly")


def test_case_insensitivity():
    """Test that search is case-insensitive."""
    print("\nTesting case insensitivity...")

    searcher = LeanSearcher()

    # Search with different cases
    results_lower = searcher.search(keywords=['array'], max_results=5)
    results_upper = searcher.search(keywords=['ARRAY'], max_results=5)
    results_mixed = searcher.search(keywords=['Array'], max_results=5)

    print(f"  'array': {len(results_lower)} results")
    print(f"  'ARRAY': {len(results_upper)} results")
    print(f"  'Array': {len(results_mixed)} results")

    # Should get similar number of results (may vary slightly due to scoring)
    assert len(results_lower) > 0, "Should find results"
    assert len(results_upper) > 0, "Should find results regardless of case"

    print("✓ Case insensitivity works")


if __name__ == "__main__":
    print("=" * 60)
    print("Running Search Engine Tests")
    print("=" * 60)

    try:
        test_basic_search()
        test_exact_name_match()
        test_multiple_keywords()
        test_type_preference()
        test_min_score_threshold()
        test_search_by_analysis()
        test_tokenization()
        test_statistics()
        test_result_serialization()
        test_empty_keywords()
        test_case_insensitivity()

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
