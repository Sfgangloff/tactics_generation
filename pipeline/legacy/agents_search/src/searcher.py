#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
searcher.py

Searches the Lean function index and ranks results by relevance.
"""

import json
from pathlib import Path
from typing import Dict, List, Any, Optional, Set
from dataclasses import dataclass
import re


@dataclass
class SearchResult:
    """A single search result with relevance score."""
    name: str
    type: str  # def, theorem, structure, class, inductive
    signature: str
    file_path: str
    docstring: Optional[str]
    description: Optional[str]  # Natural language description (from enriched index)
    source: str
    score: float
    match_reasons: List[str]  # Why this result matched

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            'name': self.name,
            'type': self.type,
            'signature': self.signature,
            'file_path': self.file_path,
            'docstring': self.docstring,
            'description': self.description,
            'source': self.source,
            'score': self.score,
            'match_reasons': self.match_reasons
        }


class LeanSearcher:
    """
    Searches Lean function index and ranks results.

    Uses multiple scoring factors (optimized for natural language search):
    - Exact name matches (10.0)
    - Partial name matches (5.0)
    - Name part matches (4.0)
    - AI description matches (3.0) ← High weight for semantic understanding
    - Signature matches (2.0)
    - Docstring matches (1.0)
    - Type relevance bonus (1.2x multiplier for preferred types)

    AI descriptions are weighted 3x higher than docstrings because they're
    specifically generated for natural language search.
    """

    def __init__(self, index_path: Optional[Path] = None, use_enriched: bool = True):
        """
        Initialize the searcher.

        Args:
            index_path: Path to index file (default: enriched_lean_index.json if use_enriched=True)
            use_enriched: Whether to use enriched index with descriptions (default: True)
        """
        if index_path is None:
            if use_enriched:
                index_path = Path(__file__).parent.parent / "data" / "enriched_lean_index.json"
            else:
                index_path = Path(__file__).parent.parent / "data" / "lean_index.json"

        self.index_path = index_path
        self.index = self._load_index()

    def _load_index(self) -> Dict[str, Any]:
        """Load the Lean function index."""
        if not self.index_path.exists():
            raise FileNotFoundError(f"Index not found: {self.index_path}")

        with open(self.index_path, 'r', encoding='utf-8') as f:
            return json.load(f)

    def search(
        self,
        keywords: List[str],
        max_results: int = 20,
        min_score: float = 0.1,
        prefer_types: Optional[List[str]] = None
    ) -> List[SearchResult]:
        """
        Search for Lean definitions matching keywords.

        Args:
            keywords: List of keywords to search for
            max_results: Maximum number of results to return
            min_score: Minimum relevance score (0-1)
            prefer_types: Prefer certain definition types (e.g., ['def', 'structure'])

        Returns:
            List of SearchResult objects, sorted by relevance
        """
        if not keywords:
            return []

        # Normalize keywords
        keywords_lower = [k.lower() for k in keywords]

        results = []

        # Search through index
        for name, defn in self.index.items():
            result = self._score_definition(name, defn, keywords_lower, prefer_types)
            if result and result.score >= min_score:
                results.append(result)

        # Sort by score (descending)
        results.sort(key=lambda r: r.score, reverse=True)

        # Return top results
        return results[:max_results]

    def _score_definition(
        self,
        name: str,
        defn: Dict[str, Any],
        keywords: List[str],
        prefer_types: Optional[List[str]] = None
    ) -> Optional[SearchResult]:
        """
        Score a single definition against keywords.

        Returns SearchResult with score, or None if no match.
        """
        score = 0.0
        match_reasons = []

        # Prepare text fields for searching
        name_lower = name.lower()
        name_parts = self._tokenize(name)  # Split on dots, underscores, camelCase
        signature_lower = defn.get('signature', '').lower()
        docstring_lower = (defn.get('docstring') or '').lower()
        description_lower = (defn.get('description') or '').lower()

        # Score each keyword
        for keyword in keywords:
            keyword_score = 0.0
            keyword_reasons = []

            # Exact name match (highest score)
            if keyword == name_lower:
                keyword_score += 10.0
                keyword_reasons.append(f"exact name match: '{keyword}'")

            # Name contains keyword
            elif keyword in name_lower:
                keyword_score += 5.0
                keyword_reasons.append(f"name contains: '{keyword}'")

            # Name part matches (e.g., "map" matches "HashMap")
            elif keyword in [p.lower() for p in name_parts]:
                keyword_score += 4.0
                keyword_reasons.append(f"name part matches: '{keyword}'")

            # Signature contains keyword
            if keyword in signature_lower:
                keyword_score += 2.0
                keyword_reasons.append(f"signature contains: '{keyword}'")

            # Docstring contains keyword
            if keyword in docstring_lower:
                keyword_score += 1.0
                keyword_reasons.append(f"docstring contains: '{keyword}'")

            # Description contains keyword (higher weight - AI-generated for search)
            if keyword in description_lower:
                keyword_score += 3.0
                keyword_reasons.append(f"description contains: '{keyword}'")

            # Add keyword score to total
            if keyword_score > 0:
                score += keyword_score
                match_reasons.extend(keyword_reasons)

        # If no matches, return None
        if score == 0:
            return None

        # Type preference bonus
        defn_type = defn.get('type', 'def')
        if prefer_types and defn_type in prefer_types:
            score *= 1.2
            match_reasons.append(f"preferred type: {defn_type}")

        # Normalize score by number of keywords (avoid bias toward more keywords)
        score = score / len(keywords)

        # Boost for having docstrings (better documented = more useful)
        if defn.get('docstring'):
            score *= 1.1

        return SearchResult(
            name=name,
            type=defn_type,
            signature=defn.get('signature', ''),
            file_path=defn.get('file_path', ''),
            docstring=defn.get('docstring'),
            description=defn.get('description'),
            source=defn.get('source', 'unknown'),
            score=score,
            match_reasons=match_reasons
        )

    def _tokenize(self, name: str) -> List[str]:
        """
        Split a name into tokens.

        Handles:
        - Dots: Nat.add -> ['Nat', 'add']
        - Underscores: hash_map -> ['hash', 'map']
        - CamelCase: HashMap -> ['Hash', 'Map']
        """
        # Split on dots
        parts = name.split('.')

        # Further split each part on underscores and camelCase
        tokens = []
        for part in parts:
            # Split on underscores
            subparts = part.split('_')
            for subpart in subparts:
                # Split on camelCase
                camel_tokens = re.findall(r'[A-Z]?[a-z]+|[A-Z]+(?=[A-Z][a-z]|\b)', subpart)
                if camel_tokens:
                    tokens.extend(camel_tokens)
                else:
                    tokens.append(subpart)

        return [t for t in tokens if t]  # Remove empty strings

    def search_by_analysis(
        self,
        analysis: Dict[str, Any],
        max_results: int = 20,
        min_score: float = 0.1
    ) -> List[SearchResult]:
        """
        Search using a full task analysis from TaskAnalyzer.

        Args:
            analysis: Result from TaskAnalyzer.analyze()
            max_results: Maximum results to return
            min_score: Minimum score threshold

        Returns:
            List of SearchResult objects
        """
        # Extract all keywords from analysis
        all_keywords = []

        # Main keywords (highest priority)
        all_keywords.extend(analysis.get('keywords', []))

        # Types (important for filtering)
        all_keywords.extend([t.lower() for t in analysis.get('types', [])])

        # Operations
        all_keywords.extend(analysis.get('operations', []))

        # Paradigm
        if analysis.get('paradigm'):
            all_keywords.append(analysis['paradigm'])

        # Determine preferred types based on analysis
        prefer_types = None
        paradigm = analysis.get('paradigm')

        # For implementation tasks, prefer defs and structures
        if paradigm in ['imperative', 'functional', 'recursive']:
            prefer_types = ['def', 'structure', 'class']

        # Search with all keywords
        return self.search(
            keywords=all_keywords,
            max_results=max_results,
            min_score=min_score,
            prefer_types=prefer_types
        )

    def get_statistics(self) -> Dict[str, Any]:
        """Get statistics about the index."""
        stats = {
            'total_definitions': len(self.index),
            'by_type': {},
            'by_source': {}
        }

        for defn in self.index.values():
            # Count by type
            defn_type = defn.get('type', 'unknown')
            stats['by_type'][defn_type] = stats['by_type'].get(defn_type, 0) + 1

            # Count by source
            source = defn.get('source', 'unknown')
            stats['by_source'][source] = stats['by_source'].get(source, 0) + 1

        return stats


def main():
    """Command-line interface for testing the searcher."""
    import argparse

    parser = argparse.ArgumentParser(description='Search Lean function index')
    parser.add_argument('keywords', nargs='+', help='Keywords to search for')
    parser.add_argument('--max-results', type=int, default=10, help='Maximum results')
    parser.add_argument('--min-score', type=float, default=0.1, help='Minimum score')
    parser.add_argument('--stats', action='store_true', help='Show index statistics')

    args = parser.parse_args()

    searcher = LeanSearcher()

    if args.stats:
        print("\nIndex Statistics:")
        print("-" * 60)
        stats = searcher.get_statistics()
        print(f"Total definitions: {stats['total_definitions']}")
        print("\nBy type:")
        for defn_type, count in sorted(stats['by_type'].items()):
            print(f"  {defn_type}: {count}")
        print("\nBy source:")
        for source, count in sorted(stats['by_source'].items()):
            print(f"  {source}: {count}")
        print()

    # Perform search
    print(f"\nSearching for: {' '.join(args.keywords)}")
    print("=" * 60)

    results = searcher.search(
        keywords=args.keywords,
        max_results=args.max_results,
        min_score=args.min_score
    )

    if not results:
        print("No results found.")
        return

    print(f"\nFound {len(results)} results:\n")

    for i, result in enumerate(results, 1):
        print(f"{i}. {result.name} (score: {result.score:.2f})")
        print(f"   Type: {result.type}")
        print(f"   Signature: {result.signature}")

        # Show description if available (prefer it over docstring for display)
        if result.description:
            desc = result.description
            if len(desc) > 120:
                desc = desc[:117] + "..."
            print(f"   Description: {desc}")
        elif result.docstring:
            # Fallback to docstring if no description
            doc = result.docstring
            if len(doc) > 100:
                doc = doc[:97] + "..."
            print(f"   Doc: {doc}")

        print(f"   Matches: {', '.join(result.match_reasons[:3])}")
        print()


if __name__ == '__main__':
    main()
