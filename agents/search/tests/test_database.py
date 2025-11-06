#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
test_database.py

Basic tests for the database module.
"""

import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from database import SearchDatabase


def test_database_init():
    """Test database initialization."""
    print("Testing database initialization...")

    # Use a temporary database
    db_path = "agents/search/data/test_search_history.db"

    # Remove if exists
    if os.path.exists(db_path):
        os.remove(db_path)

    db = SearchDatabase(db_path)

    # Check tables were created
    cursor = db.conn.cursor()
    cursor.execute("""
        SELECT name FROM sqlite_master
        WHERE type='table'
        ORDER BY name
    """)

    tables = [row[0] for row in cursor.fetchall()]

    expected_tables = ['llm_cache', 'search_queries', 'search_results', 'similar_queries']

    assert all(table in tables for table in expected_tables), f"Missing tables. Found: {tables}"

    print("✓ All tables created successfully")

    db.close()


def test_cache_operations():
    """Test cache check and record operations."""
    print("\nTesting cache operations...")

    db_path = "agents/search/data/test_search_history.db"

    if os.path.exists(db_path):
        os.remove(db_path)

    db = SearchDatabase(db_path)

    # Test cache miss
    cached = db.check_cache("multiply two numbers")
    assert cached is None, "Cache should be empty"
    print("✓ Cache miss works")

    # Record a search
    query_id = db.record_search(
        task="multiply two numbers",
        keywords=["multiply", "numbers"],
        results=[
            {
                'name': 'Nat.mul',
                'type': 'function',
                'signature': 'Nat.mul : Nat → Nat → Nat',
                'import': 'Prelude',
                'description': 'Multiplies two natural numbers',
                'relevance_score': 0.95,
                'file_path': 'Init/Data/Nat/Basic.lean'
            }
        ],
        execution_time_ms=250,
        sources=['batteries', 'std'],
        lean_version='v4.8.0'
    )

    assert query_id > 0, "Query ID should be positive"
    print(f"✓ Search recorded with query_id={query_id}")

    # Test cache hit
    cached = db.check_cache("multiply two numbers")
    assert cached is not None, "Cache should have result"
    assert cached['task'] == "multiply two numbers", "Task should match"
    assert len(cached['relevant_items']) == 1, "Should have 1 result"
    assert cached['relevant_items'][0]['name'] == 'Nat.mul', "Result name should match"
    print("✓ Cache hit works")

    db.close()


def test_llm_cache():
    """Test LLM cache operations."""
    print("\nTesting LLM cache...")

    db_path = "agents/search/data/test_search_history.db"

    if os.path.exists(db_path):
        os.remove(db_path)

    db = SearchDatabase(db_path)

    # Test cache miss
    cached = db.get_llm_cache("task_analysis", "multiply two numbers")
    assert cached is None, "LLM cache should be empty"
    print("✓ LLM cache miss works")

    # Save to cache
    db.save_llm_cache(
        cache_type="task_analysis",
        input_text="multiply two numbers",
        output={"keywords": ["multiply", "numbers"]},
        model_name="gpt-5"
    )
    print("✓ LLM cache save works")

    # Test cache hit
    cached = db.get_llm_cache("task_analysis", "multiply two numbers")
    assert cached is not None, "LLM cache should have result"
    assert cached['keywords'] == ["multiply", "numbers"], "Keywords should match"
    print("✓ LLM cache hit works")

    db.close()


def test_stats():
    """Test statistics."""
    print("\nTesting statistics...")

    db_path = "agents/search/data/test_search_history.db"

    if os.path.exists(db_path):
        os.remove(db_path)

    db = SearchDatabase(db_path)

    # Record some searches
    for i in range(3):
        db.record_search(
            task=f"test query {i}",
            keywords=["test", "query"],
            results=[],
            execution_time_ms=100 + i * 50,
            sources=['batteries'],
            lean_version='v4.8.0'
        )

    stats = db.get_search_stats()

    assert stats['total_searches'] == 3, "Should have 3 searches"
    assert stats['avg_execution_time_ms'] > 0, "Should have avg execution time"
    print(f"✓ Stats: {stats}")

    # Test most searched terms
    terms = db.get_most_searched_terms(limit=5)
    assert len(terms) > 0, "Should have search terms"
    print(f"✓ Most searched terms: {terms}")

    db.close()


if __name__ == "__main__":
    print("=" * 50)
    print("Running Database Tests")
    print("=" * 50)

    try:
        test_database_init()
        test_cache_operations()
        test_llm_cache()
        test_stats()

        print("\n" + "=" * 50)
        print("✅ All tests passed!")
        print("=" * 50)

    except AssertionError as e:
        print(f"\n❌ Test failed: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
