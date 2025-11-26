#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
task_analyzer.py

Analyzes natural language task descriptions and extracts structured keywords
for searching Lean 4 library functions.
"""

import json
import os
import re
from pathlib import Path
from typing import Dict, List, Optional, Any
from claude_agent_sdk import query
import anyio


class TaskAnalyzer:
    """
    Analyzes programming tasks and extracts search keywords using LLM.

    Uses Claude Agent SDK to convert natural language descriptions into structured
    keywords for searching Lean library functions.
    """

    def __init__(
        self,
        model: str = "claude-sonnet-4"
    ):
        """
        Initialize the task analyzer.

        Args:
            model: Model name (retained for compatibility; Claude Agent SDK may use its default)
        """
        self.model = model

        # Load prompt template
        self.system_prompt = self._load_prompt_template()

        # Note: Claude Agent SDK handles authentication automatically via environment variables

    def _load_prompt_template(self) -> str:
        """Load the system prompt template."""
        prompt_path = Path(__file__).parent.parent / "prompts" / "task_analyzer_system.txt"

        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt template not found: {prompt_path}")

        return prompt_path.read_text(encoding='utf-8')

    async def analyze_async(
        self,
        task: str,
        use_cache: bool = True,
        database=None
    ) -> Dict[str, Any]:
        """
        Async analyze a task description and extract keywords.

        Args:
            task: Natural language task description
            use_cache: Whether to use cached results if available
            database: Optional SearchDatabase instance for caching

        Returns:
            Dictionary with extracted keywords:
            {
                "keywords": List[str],
                "types": List[str],
                "operations": List[str],
                "paradigm": Optional[str],
                "domain": Optional[str]
            }
        """
        # Check cache if available
        if use_cache and database:
            cached = database.get_llm_cache("task_analysis", task)
            if cached:
                return cached

        # Call Claude Agent SDK
        try:
            # Combine system and user prompts
            full_prompt = f"{self.system_prompt}\n\n{task}\n\nPlease respond with a JSON object containing keywords, types, operations, paradigm, and domain fields."

            # Collect response from streaming API
            response_text = ""
            async for message in query(prompt=full_prompt):
                response_text += str(message)

            # Parse JSON from response
            result = json.loads(response_text)

            # Validate structure
            required_fields = ["keywords", "types", "operations", "paradigm", "domain"]
            for field in required_fields:
                if field not in result:
                    result[field] = [] if field in ["keywords", "types", "operations"] else None

            # Save to cache if database provided
            if database:
                database.save_llm_cache("task_analysis", task, result, self.model)

            return result

        except json.JSONDecodeError as e:
            print(f"Warning: Failed to parse JSON response: {e}")
            print(f"Response content: {response_text if 'response_text' in locals() else 'N/A'}")
            # Return a fallback result
            return self._extract_fallback_keywords(task)

        except Exception as e:
            print(f"Error calling Claude Agent SDK: {e}")
            # Return a fallback result
            return self._extract_fallback_keywords(task)

    def analyze(
        self,
        task: str,
        use_cache: bool = True,
        database=None
    ) -> Dict[str, Any]:
        """
        Synchronous wrapper for analyze_async.
        """
        return anyio.run(self.analyze_async, task, use_cache, database)

    def _extract_fallback_keywords(self, task: str) -> Dict[str, Any]:
        """
        Fallback keyword extraction using simple heuristics.

        Used when LLM API fails or returns invalid JSON.

        Args:
            task: Task description

        Returns:
            Dictionary with extracted keywords
        """
        # Simple tokenization
        words = re.findall(r'\w+', task.lower())

        # Filter out very common words
        stopwords = {
            'a', 'an', 'the', 'is', 'are', 'was', 'were', 'be', 'been',
            'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would',
            'should', 'could', 'can', 'may', 'might', 'must', 'that',
            'this', 'these', 'those', 'in', 'on', 'at', 'to', 'for',
            'with', 'from', 'by', 'about', 'as', 'into', 'through',
            'during', 'before', 'after', 'above', 'below', 'up', 'down',
            'out', 'off', 'over', 'under', 'again', 'further', 'then',
            'once', 'here', 'there', 'when', 'where', 'why', 'how',
            'all', 'both', 'each', 'few', 'more', 'most', 'other',
            'some', 'such', 'no', 'nor', 'not', 'only', 'own', 'same',
            'so', 'than', 'too', 'very', 'just', 'but', 'or', 'and',
            'if', 'because', 'while', 'of', 'at', 'by', 'function',
            'using', 'use', 'create', 'make', 'write', 'lean', 'programming'
        }

        keywords = [w for w in words if w not in stopwords and len(w) > 2]

        # Try to identify types (capitalized words or known types)
        known_types = {
            'nat', 'int', 'float', 'bool', 'string', 'list', 'array',
            'hashmap', 'hashset', 'option', 'either'
        }

        types = []
        for word in words:
            if word in known_types:
                types.append(word.capitalize())

        # Try to identify paradigm
        paradigm = None
        if 'imperative' in task.lower():
            paradigm = 'imperative'
        elif 'functional' in task.lower():
            paradigm = 'functional'
        elif 'recursive' in task.lower() or 'recursion' in task.lower():
            paradigm = 'recursive'

        return {
            "keywords": keywords[:8],  # Limit to 8 keywords
            "types": types,
            "operations": [],  # Can't reliably extract without LLM
            "paradigm": paradigm,
            "domain": None
        }

    def analyze_batch(
        self,
        tasks: List[str],
        use_cache: bool = True,
        database=None
    ) -> List[Dict[str, Any]]:
        """
        Analyze multiple tasks in batch.

        Args:
            tasks: List of task descriptions
            use_cache: Whether to use cached results
            database: Optional SearchDatabase instance

        Returns:
            List of analysis results
        """
        results = []
        for task in tasks:
            result = self.analyze(task, use_cache=use_cache, database=database)
            results.append(result)

        return results

    def get_all_keywords(self, analysis: Dict[str, Any]) -> List[str]:
        """
        Get all keywords from an analysis result as a flat list.

        Args:
            analysis: Result from analyze()

        Returns:
            Combined list of all keywords
        """
        all_keywords = []

        # Add main keywords
        all_keywords.extend(analysis.get("keywords", []))

        # Add types (lowercase for searching)
        all_keywords.extend([t.lower() for t in analysis.get("types", [])])

        # Add operations
        all_keywords.extend(analysis.get("operations", []))

        # Add paradigm if present
        if analysis.get("paradigm"):
            all_keywords.append(analysis["paradigm"])

        # Remove duplicates while preserving order
        seen = set()
        unique_keywords = []
        for kw in all_keywords:
            if kw not in seen:
                seen.add(kw)
                unique_keywords.append(kw)

        return unique_keywords


def main():
    """Command-line interface for testing the task analyzer."""
    import argparse

    parser = argparse.ArgumentParser(description='Analyze programming tasks')
    parser.add_argument('task', nargs='+', help='Task description')
    parser.add_argument('--model', default='gpt-4', help='OpenAI model to use')
    parser.add_argument('--no-cache', action='store_true', help='Disable caching')

    args = parser.parse_args()

    task = ' '.join(args.task)

    print(f"Analyzing task: {task}")
    print()

    analyzer = TaskAnalyzer(model=args.model)

    # Use database for caching if available
    database = None
    if not args.no_cache:
        try:
            import sys
            sys.path.insert(0, str(Path(__file__).parent))
            from database import SearchDatabase
            database = SearchDatabase()
        except ImportError:
            print("Warning: Database module not available, caching disabled")

    result = analyzer.analyze(task, use_cache=not args.no_cache, database=database)

    print("Analysis result:")
    print(json.dumps(result, indent=2))
    print()

    print("All keywords:", analyzer.get_all_keywords(result))


if __name__ == '__main__':
    main()
