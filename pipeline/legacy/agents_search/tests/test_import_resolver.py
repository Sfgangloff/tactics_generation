#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
test_import_resolver.py

Tests for the import resolver module.
"""

import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from import_resolver import ImportResolver
from searcher import LeanSearcher, SearchResult


def test_basic_resolution():
    """Test basic import resolution."""
    print("Testing basic import resolution...")

    resolver = ImportResolver()

    # Create mock search results
    results = [
        SearchResult(
            name="HashMap.insert",
            type="def",
            signature="HashMap.insert : HashMap α β → α → β → HashMap α β",
            file_path="Batteries/Data/HashMap.lean",
            docstring="Insert a key-value pair",
            source="batteries",
            score=10.0,
            match_reasons=["exact match"]
        )
    ]

    resolved = resolver.resolve(results)

    print(f"  Imports: {resolved['imports']}")
    print(f"  Opens: {resolved['opens']}")

    assert 'import Batteries' in resolved['imports'], "Should import Batteries"
    assert 'open Std' in resolved['opens'], "Should open Std for HashMap"

    print("✓ Basic resolution works")


def test_multiple_definitions():
    """Test resolution with multiple definitions."""
    print("\nTesting multiple definitions...")

    resolver = ImportResolver()

    # Create mock results from different namespaces
    results = [
        SearchResult(
            name="Array.map",
            type="def",
            signature="Array.map : Array α → (α → β) → Array β",
            file_path="Batteries/Data/Array.lean",
            docstring="Map function",
            source="batteries",
            score=10.0,
            match_reasons=["match"]
        ),
        SearchResult(
            name="List.foldl",
            type="def",
            signature="List.foldl : (β → α → β) → β → List α → β",
            file_path="Batteries/Data/List.lean",
            docstring="Fold left",
            source="batteries",
            score=9.0,
            match_reasons=["match"]
        )
    ]

    resolved = resolver.resolve(results)

    print(f"  Imports: {resolved['imports']}")
    print(f"  Opens: {resolved['opens']}")

    assert 'import Batteries' in resolved['imports'], "Should import Batteries"
    assert len(resolved['by_definition']) == 2, "Should have info for both definitions"

    print("✓ Multiple definitions work")


def test_minimal_imports():
    """Test getting minimal import statements."""
    print("\nTesting minimal imports...")

    resolver = ImportResolver()

    results = [
        SearchResult(
            name="HashSet.insert",
            type="def",
            signature="HashSet.insert : HashSet α → α → HashSet α",
            file_path="Batteries/Data/HashSet.lean",
            docstring="Insert element",
            source="batteries",
            score=10.0,
            match_reasons=["match"]
        )
    ]

    # With opens
    imports_with_opens = resolver.get_minimal_imports(results, include_opens=True)
    print(f"  With opens: {imports_with_opens}")

    # Without opens
    imports_without_opens = resolver.get_minimal_imports(results, include_opens=False)
    print(f"  Without opens: {imports_without_opens}")

    assert 'import Batteries' in imports_with_opens
    assert 'open Std' in imports_with_opens
    assert 'open Std' not in imports_without_opens

    print("✓ Minimal imports work")


def test_usage_hints():
    """Test usage hint generation."""
    print("\nTesting usage hint generation...")

    resolver = ImportResolver()

    test_cases = [
        (
            SearchResult(
                name="HashMap.insert",
                type="def",
                signature="HashMap.insert : HashMap α β → α → β → HashMap α β",
                file_path="",
                docstring="",
                source="batteries",
                score=10.0,
                match_reasons=[]
            ),
            "HashMap.insert arg1 arg2 ..."
        ),
        (
            SearchResult(
                name="BinaryHeap",
                type="structure",
                signature="BinaryHeap",
                file_path="",
                docstring="",
                source="batteries",
                score=10.0,
                match_reasons=[]
            ),
            "BinaryHeap.mk ..."
        ),
    ]

    for result, expected_pattern in test_cases:
        hint = resolver._generate_usage_hint(result)
        print(f"  {result.name} ({result.type}): {hint}")
        assert result.name.split('.')[-1] in hint or result.type in ['structure', 'class'], \
            f"Hint should contain definition name or be structure/class"

    print("✓ Usage hints work")


def test_format_for_lean_file():
    """Test formatting imports for Lean file."""
    print("\nTesting Lean file formatting...")

    resolver = ImportResolver()

    results = [
        SearchResult(
            name="HashMap.ofList",
            type="def",
            signature="HashMap.ofList : List (α × β) → HashMap α β",
            file_path="",
            docstring="",
            source="batteries",
            score=10.0,
            match_reasons=[]
        )
    ]

    formatted = resolver.format_for_lean_file(results, add_comments=True)

    print("  Formatted output:")
    print("-" * 60)
    for line in formatted.split('\n'):
        print(f"  {line}")
    print("-" * 60)

    assert 'import Batteries' in formatted
    assert 'open Std' in formatted
    assert '-- Imports for search results' in formatted
    assert '-- Usage hints:' in formatted

    print("✓ Lean file formatting works")


def test_import_explanation():
    """Test import explanation generation."""
    print("\nTesting import explanation...")

    resolver = ImportResolver()

    result = SearchResult(
        name="HashMap.insert",
        type="def",
        signature="HashMap.insert : HashMap α β → α → β → HashMap α β",
        file_path="",
        docstring="",
        source="batteries",
        score=10.0,
        match_reasons=[]
    )

    explanation = resolver.explain_import("HashMap.insert", result)

    print(f"  Explanation: {explanation}")

    assert 'HashMap' in explanation, "Should mention namespace"
    assert 'import' in explanation.lower(), "Should mention import"

    print("✓ Import explanation works")


def test_root_prefix_handling():
    """Test handling of _root_ prefix."""
    print("\nTesting _root_ prefix handling...")

    resolver = ImportResolver()

    results = [
        SearchResult(
            name="_root_.Batteries.HashMap",
            type="structure",
            signature="_root_.Batteries.HashMap",
            file_path="",
            docstring="",
            source="batteries",
            score=10.0,
            match_reasons=[]
        )
    ]

    resolved = resolver.resolve(results)

    print(f"  Imports: {resolved['imports']}")
    print(f"  Opens: {resolved['opens']}")

    assert 'import Batteries' in resolved['imports']

    # Check usage hint doesn't include _root_
    hint = resolved['by_definition']['_root_.Batteries.HashMap']['usage_example']
    print(f"  Usage hint: {hint}")
    assert '_root_' not in hint, "Usage hint should not contain _root_"

    print("✓ _root_ prefix handling works")


def test_with_real_search():
    """Test with real search results."""
    print("\nTesting with real search results...")

    searcher = LeanSearcher()
    resolver = ImportResolver()

    # Search for hash map functions
    results = searcher.search(['hashmap', 'insert'], max_results=3)

    if not results:
        print("  ⚠ No search results, skipping test")
        return

    print(f"  Found {len(results)} results")

    resolved = resolver.resolve(results)

    print(f"  Imports: {resolved['imports']}")
    print(f"  Opens: {resolved['opens']}")

    assert len(resolved['imports']) > 0, "Should have some imports"
    assert len(resolved['by_definition']) == len(results), "Should have info for all results"

    # Test formatting
    formatted = resolver.format_for_lean_file(results, add_comments=False)
    print("\n  Formatted header:")
    print(formatted)

    print("✓ Real search integration works")


if __name__ == "__main__":
    print("=" * 60)
    print("Running Import Resolver Tests")
    print("=" * 60)

    try:
        test_basic_resolution()
        test_multiple_definitions()
        test_minimal_imports()
        test_usage_hints()
        test_format_for_lean_file()
        test_import_explanation()
        test_root_prefix_handling()
        test_with_real_search()

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
