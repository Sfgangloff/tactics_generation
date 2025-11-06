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
from openai import OpenAI


class TaskAnalyzer:
    """
    Analyzes programming tasks and extracts search keywords using LLM.

    Uses OpenAI API to convert natural language descriptions into structured
    keywords for searching Lean library functions.
    """

    def __init__(
        self,
        model: str = "gpt-4o-mini",
        api_key: Optional[str] = None
    ):
        """
        Initialize the task analyzer.

        Args:
            model: OpenAI model to use (default: gpt-4o-mini)
            api_key: OpenAI API key (if None, reads from openai_key.txt or env)
        """
        self.model = model

        # Load API key
        if api_key is None:
            api_key = self._load_api_key()

        self.client = OpenAI(api_key=api_key)

        # Load prompt template
        self.system_prompt = self._load_prompt_template()

    def _load_api_key(self) -> str:
        """Load OpenAI API key from file or environment."""
        # Try file first
        project_root = Path(__file__).parent.parent.parent.parent
        key_file = project_root / "openai_key.txt"

        if key_file.exists():
            return key_file.read_text().strip()

        # Try environment variable
        api_key = os.environ.get("OPENAI_API_KEY")
        if api_key:
            return api_key

        raise ValueError(
            "OpenAI API key not found. "
            "Please create openai_key.txt in project root or set OPENAI_API_KEY env var."
        )

    def _load_prompt_template(self) -> str:
        """Load the system prompt template."""
        prompt_path = Path(__file__).parent.parent / "prompts" / "task_analyzer_system.txt"

        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt template not found: {prompt_path}")

        return prompt_path.read_text(encoding='utf-8')

    def analyze(
        self,
        task: str,
        use_cache: bool = True,
        database=None
    ) -> Dict[str, Any]:
        """
        Analyze a task description and extract keywords.

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

        # Call OpenAI API
        try:
            # Prepare API call parameters
            api_params = {
                "model": self.model,
                "messages": [
                    {"role": "system", "content": self.system_prompt},
                    {"role": "user", "content": task}
                ],
                "temperature": 0.0  # Deterministic output
            }

            # Only use JSON mode for models that support it
            if "gpt-4o" in self.model or "gpt-3.5-turbo" in self.model:
                api_params["response_format"] = {"type": "json_object"}

            response = self.client.chat.completions.create(**api_params)

            # Extract response
            content = response.choices[0].message.content

            # Parse JSON
            result = json.loads(content)

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
            print(f"Response content: {content}")
            # Return a fallback result
            return self._extract_fallback_keywords(task)

        except Exception as e:
            print(f"Error calling OpenAI API: {e}")
            # Return a fallback result
            return self._extract_fallback_keywords(task)

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
