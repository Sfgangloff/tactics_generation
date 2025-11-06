#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
search_agent.py

Main search agent that orchestrates all components to find relevant Lean definitions.
"""

import json
import time
from pathlib import Path
from typing import Dict, List, Any, Optional
import sys

# Add current directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

from task_analyzer import TaskAnalyzer
from searcher import LeanSearcher
from import_resolver import ImportResolver
from database import SearchDatabase


class SearchAgent:
    """
    Main search agent that orchestrates the search pipeline.

    Pipeline:
    1. Check cache for exact match
    2. Analyze task with LLM (extract keywords)
    3. Search enriched index
    4. Resolve imports
    5. Format results
    6. Record in database
    """

    def __init__(
        self,
        database_path: Optional[str] = None,
        model: str = "gpt-4o-mini"
    ):
        """
        Initialize the search agent.

        Args:
            database_path: Path to search history database
            model: OpenAI model for task analysis
        """
        # Set up database
        if database_path is None:
            database_path = str(Path(__file__).parent.parent / "data" / "search_history.db")

        self.database = SearchDatabase(database_path)

        # Initialize components
        self.task_analyzer = TaskAnalyzer(model=model)
        self.searcher = LeanSearcher(use_enriched=True)
        self.import_resolver = ImportResolver()

    def search(
        self,
        task: str,
        max_results: int = 10,
        use_cache: bool = True
    ) -> Dict[str, Any]:
        """
        Search for Lean definitions relevant to a task.

        Args:
            task: Natural language task description
            max_results: Maximum number of results to return
            use_cache: Whether to use cached results

        Returns:
            Dictionary with search results and metadata
        """
        start_time = time.time()

        # Check cache
        if use_cache:
            cached = self.database.check_cache(task)
            if cached:
                execution_time = (time.time() - start_time) * 1000
                return {
                    'query_id': cached['query_id'],
                    'task': task,
                    'results': cached['relevant_items'],  # Database returns 'relevant_items'
                    'execution_time_ms': execution_time,
                    'from_cache': True
                }

        # Analyze task
        analysis = self.task_analyzer.analyze(
            task,
            use_cache=True,
            database=self.database
        )

        # Get all keywords
        keywords = self.task_analyzer.get_all_keywords(analysis)

        # Search
        search_results = self.searcher.search_by_analysis(
            analysis,
            max_results=max_results
        )

        # Resolve imports for each result
        import_info = self.import_resolver.resolve(search_results)

        # Format results
        formatted_results = []
        for result in search_results:
            result_dict = result.to_dict()

            # Add import info (convert lists to strings for database)
            imports = import_info['by_definition'][result.name]['imports']
            opens = import_info['by_definition'][result.name]['opens']

            result_dict['import'] = ', '.join(imports) if imports else ''
            result_dict['opens'] = ', '.join(opens) if opens else ''
            result_dict['usage_hint'] = import_info['by_definition'][result.name]['usage_example']
            result_dict['relevance_score'] = result.score  # Add relevance_score field for database

            formatted_results.append(result_dict)

        # Calculate execution time
        execution_time = (time.time() - start_time) * 1000

        # Record in database
        query_id = self.database.record_search(
            task=task,
            keywords=json.dumps(keywords),  # Convert to JSON string
            results=formatted_results,
            execution_time_ms=int(execution_time),
            sources='batteries',
            lean_version='4.0'  # TODO: Get actual Lean version
        )

        return {
            'query_id': query_id,
            'task': task,
            'analysis': analysis,
            'results': formatted_results,
            'execution_time_ms': execution_time,
            'from_cache': False
        }

    def format_results_for_display(self, search_response: Dict[str, Any]) -> str:
        """
        Format search results for command-line display.

        Args:
            search_response: Response from search()

        Returns:
            Formatted string for display
        """
        lines = []

        # Header
        lines.append("=" * 70)
        lines.append("Search Results")
        lines.append("=" * 70)
        lines.append(f"Task: {search_response['task']}")
        lines.append(f"Found: {len(search_response['results'])} results")
        lines.append(f"Time: {search_response['execution_time_ms']:.1f}ms")

        if search_response['from_cache']:
            lines.append("Source: Cache (instant)")
        else:
            lines.append("Source: Fresh search")

        lines.append("")

        # Results
        for i, result in enumerate(search_response['results'], 1):
            lines.append("-" * 70)
            score = result.get('score') or result.get('relevance_score', 0)
            lines.append(f"{i}. {result['name']} (relevance: {score:.2f})")
            lines.append("")
            lines.append(f"   Type: {result['type']}")
            lines.append(f"   Signature: {result['signature']}")
            lines.append("")

            # Description
            if result.get('description'):
                desc = result['description']
                # Wrap long descriptions
                if len(desc) > 60:
                    words = desc.split()
                    current_line = "   Description: "
                    for word in words:
                        if len(current_line) + len(word) + 1 > 70:
                            lines.append(current_line)
                            current_line = "                " + word
                        else:
                            current_line += " " + word if current_line.endswith(" ") or current_line.endswith(":") else word
                    lines.append(current_line)
                else:
                    lines.append(f"   Description: {desc}")
                lines.append("")

            # Import info
            if result.get('import'):
                imports_str = result['import']
                lines.append(f"   Import: {imports_str}")

            if result.get('opens'):
                opens_str = result['opens']
                if opens_str:
                    lines.append(f"   Open: {opens_str}")

            # Usage hint
            if result.get('usage_hint'):
                lines.append(f"   Usage: {result['usage_hint']}")

            lines.append("")

        lines.append("=" * 70)

        return "\n".join(lines)

    def get_statistics(self) -> Dict[str, Any]:
        """Get search agent statistics."""
        return self.database.get_search_stats()

    def close(self):
        """Close database connection."""
        self.database.close()


def main():
    """Command-line interface for the search agent."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Search for relevant Lean 4 definitions',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic search
  python3 search_agent.py --task "multiply two natural numbers"

  # Search with more results
  python3 search_agent.py --task "iterate over array" --max-results 20

  # Disable cache
  python3 search_agent.py --task "find maximum" --no-cache

  # Export to JSON
  python3 search_agent.py --task "hash map operations" --output results.json

  # View statistics
  python3 search_agent.py --stats

  # Rebuild index (run indexer)
  python3 search_agent.py --rebuild-index

  # Enrich index with descriptions
  python3 search_agent.py --enrich-index
        """
    )

    # Main operations
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        '--task',
        type=str,
        help='Natural language task description'
    )
    group.add_argument(
        '--stats',
        action='store_true',
        help='Show search statistics'
    )
    group.add_argument(
        '--rebuild-index',
        action='store_true',
        help='Rebuild the Lean function index'
    )
    group.add_argument(
        '--enrich-index',
        action='store_true',
        help='Enrich index with descriptions (one-time process)'
    )

    # Search options
    parser.add_argument(
        '--max-results',
        type=int,
        default=10,
        help='Maximum number of results (default: 10)'
    )
    parser.add_argument(
        '--no-cache',
        action='store_true',
        help='Disable cache lookup'
    )
    parser.add_argument(
        '--output',
        type=str,
        help='Save results to JSON file'
    )
    parser.add_argument(
        '--model',
        type=str,
        default='gpt-4o-mini',
        help='OpenAI model for task analysis (default: gpt-4o-mini)'
    )

    args = parser.parse_args()

    # Handle special operations
    if args.stats:
        agent = SearchAgent()
        stats = agent.get_statistics()
        print("\n" + "=" * 60)
        print("Search Agent Statistics")
        print("=" * 60)
        print(f"Total searches: {stats['total_searches']}")
        print(f"Avg execution time: {stats['avg_execution_time_ms']:.1f}ms")
        print(f"Cache hit rate: {stats['cache_hit_rate_percent']:.1f}%")
        print(f"LLM cache entries: {stats['llm_cache_entries']}")
        print(f"LLM cache hits: {stats['llm_cache_hits']}")
        agent.close()
        return

    if args.rebuild_index:
        print("Rebuilding Lean function index...")
        print("Running indexer...")
        import subprocess
        result = subprocess.run(
            ['python3', 'agents/search/src/lean_indexer.py'],
            capture_output=True,
            text=True
        )
        print(result.stdout)
        if result.returncode != 0:
            print("Error:", result.stderr)
            sys.exit(1)
        print("\n✅ Index rebuilt successfully!")
        return

    if args.enrich_index:
        print("Enriching index with descriptions...")
        print("This will call OpenAI API for definitions without good docstrings.")
        print("")
        import subprocess
        result = subprocess.run(
            [
                'python3',
                'agents/search/src/enrich_index_descriptions.py',
                '--input', 'agents/search/data/lean_index.json',
                '--output', 'agents/search/data/enriched_lean_index.json'
            ],
            text=True
        )
        if result.returncode != 0:
            print("\n❌ Enrichment failed")
            sys.exit(1)
        print("\n✅ Index enriched successfully!")
        return

    # Require task for search
    if not args.task:
        parser.print_help()
        return

    # Perform search
    print(f"\nSearching for: {args.task}")
    print("Please wait...")
    print()

    agent = SearchAgent(model=args.model)

    try:
        results = agent.search(
            task=args.task,
            max_results=args.max_results,
            use_cache=not args.no_cache
        )

        # Display results
        formatted = agent.format_results_for_display(results)
        print(formatted)

        # Save to file if requested
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                json.dump(results, f, indent=2, ensure_ascii=False)
            print(f"\n✅ Results saved to: {args.output}")

    finally:
        agent.close()


if __name__ == '__main__':
    main()
