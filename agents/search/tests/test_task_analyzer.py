#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
test_task_analyzer.py

Tests for the task analyzer module.
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from task_analyzer import TaskAnalyzer
from database import SearchDatabase


def test_fallback_extraction():
    """Test fallback keyword extraction (no API call)."""
    print("Testing fallback keyword extraction...")

    analyzer = TaskAnalyzer()

    # Test with a simple task
    task = "multiply two natural numbers"

    # Use fallback directly
    result = analyzer._extract_fallback_keywords(task)

    print(f"  Task: {task}")
    print(f"  Keywords: {result['keywords']}")

    assert len(result['keywords']) > 0, "Should extract some keywords"
    assert 'multiply' in result['keywords'], "Should find 'multiply'"
    assert 'numbers' in result['keywords'] or 'natural' in result['keywords'], "Should find 'numbers' or 'natural'"

    print("✓ Fallback extraction works")


def test_api_key_loading():
    """Test API key loading."""
    print("\nTesting API key loading...")

    try:
        analyzer = TaskAnalyzer()
        print("✓ API key loaded successfully")
        return True
    except ValueError as e:
        print(f"  ⚠ API key not found: {e}")
        print("  This is OK if you haven't set up OpenAI key yet")
        return False


def test_with_llm():
    """Test with actual LLM call (requires API key)."""
    print("\nTesting with LLM...")

    # Check if API key is available
    try:
        analyzer = TaskAnalyzer(model="gpt-4")
    except ValueError:
        print("  ⚠ Skipping LLM test (no API key)")
        return

    # Test tasks
    test_tasks = [
        "multiply two natural numbers",
        "iterate over an array using imperative programming",
        "find the maximum element in a list"
    ]

    # Create database for caching
    db_path = "agents/search/data/test_search_history.db"
    if os.path.exists(db_path):
        os.remove(db_path)

    db = SearchDatabase(db_path)

    print("\n  Running test queries (this will call OpenAI API)...")

    for task in test_tasks:
        print(f"\n  Task: {task}")

        result = analyzer.analyze(task, use_cache=True, database=db)

        print(f"    Keywords: {result.get('keywords', [])}")
        print(f"    Types: {result.get('types', [])}")
        print(f"    Operations: {result.get('operations', [])}")
        print(f"    Paradigm: {result.get('paradigm')}")
        print(f"    Domain: {result.get('domain')}")

        # Validate structure
        assert 'keywords' in result, "Should have keywords"
        assert 'types' in result, "Should have types"
        assert 'operations' in result, "Should have operations"

        assert len(result['keywords']) > 0, "Should extract at least one keyword"

    # Test caching
    print("\n  Testing cache hit...")
    result_cached = analyzer.analyze(test_tasks[0], use_cache=True, database=db)
    assert result_cached == result, "Cached result should match"
    print("  ✓ Cache works")

    # Clean up
    db.close()
    os.remove(db_path)

    print("\n✓ LLM analysis works")


def test_get_all_keywords():
    """Test getting all keywords as flat list."""
    print("\nTesting get_all_keywords...")

    analyzer = TaskAnalyzer()

    analysis = {
        "keywords": ["multiply", "numbers"],
        "types": ["Nat", "Int"],
        "operations": ["multiplication"],
        "paradigm": "functional",
        "domain": "arithmetic"
    }

    all_keywords = analyzer.get_all_keywords(analysis)

    print(f"  Analysis: {analysis}")
    print(f"  All keywords: {all_keywords}")

    assert 'multiply' in all_keywords, "Should include main keywords"
    assert 'nat' in all_keywords, "Should include types (lowercase)"
    assert 'multiplication' in all_keywords, "Should include operations"
    assert 'functional' in all_keywords, "Should include paradigm"

    # Check no duplicates
    assert len(all_keywords) == len(set(all_keywords)), "Should not have duplicates"

    print("✓ get_all_keywords works")


if __name__ == "__main__":
    print("=" * 60)
    print("Running Task Analyzer Tests")
    print("=" * 60)

    try:
        test_fallback_extraction()
        has_api_key = test_api_key_loading()

        # Skip LLM test by default (can be enabled via command line)
        import sys
        run_llm = '--with-llm' in sys.argv

        if has_api_key and run_llm:
            print("\n  Running LLM test (--with-llm flag provided)...")
            test_with_llm()
        else:
            if has_api_key:
                print("\n  ⚠ Skipping LLM test (use --with-llm flag to run)")
            else:
                print("\n  ⚠ Skipping LLM test (no API key)")

        test_get_all_keywords()

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
