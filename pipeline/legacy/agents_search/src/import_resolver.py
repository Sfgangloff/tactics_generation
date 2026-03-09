#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
import_resolver.py

Determines the correct import statements for Lean definitions.
"""

from pathlib import Path
from typing import List, Set, Dict, Any, Optional
import re


class ImportResolver:
    """
    Resolves import statements for Lean definitions.

    For Batteries library, most definitions require:
    - import Batteries
    - open Std (for HashMap, HashSet, etc.)

    This module handles both simple cases and edge cases.
    """

    def __init__(self):
        """Initialize the import resolver."""
        # Known namespace to import mappings
        self.namespace_imports = {
            'Batteries': 'import Batteries',
            'Std': 'import Batteries',  # Std is part of Batteries
            'Array': 'import Batteries',
            'List': 'import Batteries',
            'HashMap': 'import Batteries',
            'HashSet': 'import Batteries',
            'BinaryHeap': 'import Batteries',
            'RBMap': 'import Batteries',
            'RBSet': 'import Batteries',
        }

        # Common opens for convenience
        self.common_opens = [
            'open Std'  # For HashMap, HashSet, etc.
        ]

    def resolve(self, search_results: List[Any]) -> Dict[str, Any]:
        """
        Resolve imports for a list of search results.

        Args:
            search_results: List of SearchResult objects

        Returns:
            Dictionary with:
            {
                'imports': List[str],  # Import statements
                'opens': List[str],    # Open statements
                'by_definition': Dict[str, Dict]  # Per-definition info
            }
        """
        imports = set()
        opens = set()
        by_definition = {}

        for result in search_results:
            # Determine import for this definition
            import_info = self._resolve_single(result)

            imports.update(import_info['imports'])
            opens.update(import_info['opens'])

            by_definition[result.name] = {
                'imports': list(import_info['imports']),
                'opens': list(import_info['opens']),
                'namespace': import_info['namespace'],
                'usage_example': self._generate_usage_hint(result)
            }

        return {
            'imports': sorted(list(imports)),
            'opens': sorted(list(opens)),
            'by_definition': by_definition
        }

    def _resolve_single(self, result: Any) -> Dict[str, Any]:
        """
        Resolve imports for a single definition.

        Args:
            result: A SearchResult object

        Returns:
            Dictionary with imports, opens, and namespace
        """
        imports = set()
        opens = set()
        namespace = None

        # Extract namespace from definition name
        name_parts = result.name.split('.')

        # Special handling for _root_ prefix
        if name_parts[0] == '_root_':
            name_parts = name_parts[1:]

        if len(name_parts) > 1:
            # Has a namespace (e.g., Nat.add, HashMap.insert)
            namespace = name_parts[0]

            # Determine import based on namespace
            if namespace in self.namespace_imports:
                imports.add(self.namespace_imports[namespace])
            else:
                # Default to Batteries
                imports.add('import Batteries')

            # Add common opens for frequently used namespaces
            if namespace in ['HashMap', 'HashSet', 'BinaryHeap', 'RBMap', 'RBSet']:
                opens.add('open Std')

        else:
            # No namespace, likely a top-level definition
            # Check source
            source = getattr(result, 'source', 'unknown')

            if source == 'batteries':
                imports.add('import Batteries')
                opens.add('open Std')
            else:
                # Default
                imports.add('import Batteries')

        return {
            'imports': imports,
            'opens': opens,
            'namespace': namespace
        }

    def _generate_usage_hint(self, result: Any) -> str:
        """
        Generate a simple usage hint for a definition.

        Args:
            result: A SearchResult object

        Returns:
            String with usage hint
        """
        name = result.name
        defn_type = result.type

        # Remove _root_ prefix for display
        if name.startswith('_root_.'):
            name = name[7:]

        if defn_type == 'def':
            # Function call
            if '→' in result.signature:
                return f"{name} arg1 arg2 ..."
            else:
                return f"{name}"

        elif defn_type == 'structure':
            # Constructor
            return f"{name}.mk ..."

        elif defn_type == 'class':
            # Usually used in type constraints
            return f"[{name} α]"

        elif defn_type == 'inductive':
            # Constructor
            return f"{name}.constructor ..."

        elif defn_type == 'theorem':
            # Theorem application
            return f"{name} proof1 proof2 ..."

        else:
            return name

    def get_minimal_imports(
        self,
        search_results: List[Any],
        include_opens: bool = True
    ) -> List[str]:
        """
        Get minimal set of import statements for search results.

        Args:
            search_results: List of SearchResult objects
            include_opens: Whether to include 'open' statements

        Returns:
            List of import/open statements
        """
        resolved = self.resolve(search_results)

        statements = []
        statements.extend(resolved['imports'])

        if include_opens:
            statements.extend(resolved['opens'])

        return statements

    def format_for_lean_file(
        self,
        search_results: List[Any],
        add_comments: bool = True
    ) -> str:
        """
        Format imports as a complete header for a Lean file.

        Args:
            search_results: List of SearchResult objects
            add_comments: Whether to add explanatory comments

        Returns:
            Formatted import section
        """
        resolved = self.resolve(search_results)

        lines = []

        if add_comments:
            lines.append("-- Imports for search results")
            lines.append("")

        # Add imports
        for imp in resolved['imports']:
            lines.append(imp)

        if resolved['opens']:
            lines.append("")

        # Add opens
        for opn in resolved['opens']:
            lines.append(opn)

        if add_comments and resolved['by_definition']:
            lines.append("")
            lines.append("-- Usage hints:")
            for name, info in sorted(resolved['by_definition'].items()):
                lines.append(f"-- {info['usage_example']}")

        return '\n'.join(lines)

    def explain_import(self, definition_name: str, search_result: Any) -> str:
        """
        Explain why a particular import is needed.

        Args:
            definition_name: Name of the definition
            search_result: SearchResult object

        Returns:
            Human-readable explanation
        """
        import_info = self._resolve_single(search_result)

        explanation_parts = []

        if import_info['namespace']:
            explanation_parts.append(
                f"'{definition_name}' is in the {import_info['namespace']} namespace."
            )

        if import_info['imports']:
            imports_list = ', '.join(f"'{i}'" for i in import_info['imports'])
            explanation_parts.append(f"Requires: {imports_list}.")

        if import_info['opens']:
            opens_list = ', '.join(f"'{o}'" for o in import_info['opens'])
            explanation_parts.append(f"Recommended: {opens_list}.")

        if not explanation_parts:
            explanation_parts.append(
                "This is a built-in definition, no import needed."
            )

        return ' '.join(explanation_parts)


def main():
    """Command-line interface for testing the import resolver."""
    import argparse
    import sys

    # Add searcher to path
    sys.path.insert(0, str(Path(__file__).parent))
    from searcher import LeanSearcher

    parser = argparse.ArgumentParser(description='Resolve imports for Lean definitions')
    parser.add_argument('keywords', nargs='+', help='Keywords to search for')
    parser.add_argument('--max-results', type=int, default=5, help='Maximum search results')
    parser.add_argument('--no-opens', action='store_true', help='Exclude open statements')
    parser.add_argument('--explain', action='store_true', help='Explain each import')

    args = parser.parse_args()

    # Search for definitions
    print(f"Searching for: {' '.join(args.keywords)}")
    print("=" * 60)

    searcher = LeanSearcher()
    results = searcher.search(args.keywords, max_results=args.max_results)

    if not results:
        print("No results found.")
        return

    print(f"\nFound {len(results)} results\n")

    # Resolve imports
    resolver = ImportResolver()
    resolved = resolver.resolve(results)

    # Show imports
    print("Required imports:")
    print("-" * 60)
    for imp in resolved['imports']:
        print(imp)

    if resolved['opens']:
        print()
        for opn in resolved['opens']:
            print(opn)

    # Show per-definition info
    if args.explain:
        print("\n" + "=" * 60)
        print("Import explanations:")
        print("=" * 60)

        for result in results:
            print(f"\n{result.name}:")
            explanation = resolver.explain_import(result.name, result)
            print(f"  {explanation}")
            print(f"  Usage: {resolved['by_definition'][result.name]['usage_example']}")

    # Show complete file header
    print("\n" + "=" * 60)
    print("Complete Lean file header:")
    print("=" * 60)
    print()
    print(resolver.format_for_lean_file(results, add_comments=True))


if __name__ == '__main__':
    main()
