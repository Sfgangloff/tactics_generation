#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
enrich_index_descriptions.py

One-time batch process to add natural language descriptions to the Lean index.
This runs once after building the index, not during searches.
"""

import json
from pathlib import Path
from typing import Dict, List, Any, Optional
from openai import OpenAI
import os


class IndexEnricher:
    """
    Enriches the Lean index with natural language descriptions.

    This is a one-time batch process. It:
    1. Loads the raw index
    2. For each definition without a good docstring:
       - Loads source code context
       - Calls LLM to generate description
    3. Saves enriched index with descriptions
    """

    def __init__(
        self,
        model: str = "gpt-4o-mini",
        api_key: Optional[str] = None
    ):
        """
        Initialize the index enricher.

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

        # Statistics
        self.stats = {
            'total_definitions': 0,
            'kept_docstrings': 0,
            'generated_descriptions': 0,
            'failed_generations': 0
        }

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
        prompt_path = Path(__file__).parent.parent / "prompts" / "description_enricher_system.txt"

        if not prompt_path.exists():
            raise FileNotFoundError(f"Prompt template not found: {prompt_path}")

        return prompt_path.read_text(encoding='utf-8')

    def load_source_context(
        self,
        file_path: str,
        line_number: int,
        context_lines: int = 10
    ) -> Optional[str]:
        """
        Load source code context around a definition.

        Args:
            file_path: Path to the Lean source file
            line_number: Line number of the definition
            context_lines: Number of lines before/after to include

        Returns:
            Source code context, or None if file not found
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            # Calculate range
            start = max(0, line_number - context_lines - 1)  # -1 for 0-indexing
            end = min(len(lines), line_number + context_lines)

            # Extract context
            context = ''.join(lines[start:end])
            return context

        except FileNotFoundError:
            print(f"  Warning: Source file not found: {file_path}")
            return None
        except Exception as e:
            print(f"  Warning: Error reading {file_path}: {e}")
            return None

    def needs_description(self, definition: Dict[str, Any]) -> bool:
        """
        Check if a definition needs a generated description.

        Args:
            definition: Definition dict from index

        Returns:
            True if needs description, False if has good docstring
        """
        docstring = definition.get('docstring')

        # No docstring → needs description
        if not docstring:
            return True

        # Very short docstring → probably needs better description
        if len(docstring.strip()) < 20:
            return True

        # Has good docstring
        return False

    def generate_description(
        self,
        name: str,
        definition: Dict[str, Any],
        source_context: Optional[str] = None
    ) -> str:
        """
        Generate a description for a definition.

        Args:
            name: Name of the definition
            definition: Definition dict from index
            source_context: Optional source code context

        Returns:
            Generated description string
        """
        # Prepare user message
        user_message = self._format_user_message(name, definition, source_context)

        try:
            # Prepare API call parameters
            api_params = {
                "model": self.model,
                "messages": [
                    {"role": "system", "content": self.system_prompt},
                    {"role": "user", "content": user_message}
                ],
                "temperature": 0.2,  # Low temperature for consistency
                "max_tokens": 200  # Keep descriptions concise
            }

            response = self.client.chat.completions.create(**api_params)

            # Extract response
            description = response.choices[0].message.content.strip()

            return description

        except Exception as e:
            print(f"    Error generating description: {e}")
            return self._generate_fallback_description(name, definition)

    def _format_user_message(
        self,
        name: str,
        definition: Dict[str, Any],
        source_context: Optional[str]
    ) -> str:
        """
        Format the user message for the LLM.

        Args:
            name: Definition name
            definition: Definition dict
            source_context: Optional source code

        Returns:
            Formatted message string
        """
        lines = [
            f"Name: {name}",
            f"Type: {definition.get('type', 'unknown')}",
            f"Signature: {definition.get('signature', 'unknown')}"
        ]

        if definition.get('docstring'):
            lines.append(f"Existing docstring: {definition['docstring']}")

        if source_context:
            lines.append(f"\nSource code context:\n```lean\n{source_context}\n```")

        return "\n".join(lines)

    def _generate_fallback_description(
        self,
        name: str,
        definition: Dict[str, Any]
    ) -> str:
        """
        Generate a simple fallback description without LLM.

        Args:
            name: Definition name
            definition: Definition dict

        Returns:
            Simple description string
        """
        # If has docstring, use it
        if definition.get('docstring'):
            return definition['docstring']

        # Otherwise, generate based on type
        defn_type = definition.get('type', 'definition')
        signature = definition.get('signature', '')

        if defn_type == 'def':
            return f"A function: {signature}"
        elif defn_type == 'structure':
            return f"A data structure: {signature}"
        elif defn_type == 'class':
            return f"A type class: {signature}"
        elif defn_type == 'theorem':
            return f"A theorem: {signature}"
        elif defn_type == 'inductive':
            return f"An inductive type: {signature}"
        else:
            return signature or f"A Lean {defn_type}"

    def enrich_index(
        self,
        index_path: Path,
        output_path: Path,
        load_source: bool = True,
        skip_existing: bool = True
    ):
        """
        Enrich the entire index with descriptions.

        Args:
            index_path: Path to raw index JSON
            output_path: Path to save enriched index
            load_source: Whether to load source code context
            skip_existing: Whether to skip definitions that already have 'description' field
        """
        print("=" * 60)
        print("Index Description Enrichment")
        print("=" * 60)
        print()

        # Load index
        print(f"Loading index from: {index_path}")
        with open(index_path, 'r', encoding='utf-8') as f:
            index = json.load(f)

        self.stats['total_definitions'] = len(index)
        print(f"Found {len(index)} definitions")
        print()

        # Process each definition
        print("Processing definitions...")
        print("-" * 60)

        for i, (name, defn) in enumerate(index.items(), 1):
            # Skip if already has description and skip_existing is True
            if skip_existing and 'description' in defn:
                print(f"{i}/{len(index)}: {name} [SKIP - has description]")
                self.stats['kept_docstrings'] += 1
                continue

            # Check if needs description
            if not self.needs_description(defn):
                # Keep existing docstring as description
                defn['description'] = defn['docstring']
                print(f"{i}/{len(index)}: {name} [KEEP docstring]")
                self.stats['kept_docstrings'] += 1
                continue

            # Generate description
            print(f"{i}/{len(index)}: {name} [GENERATE]")

            # Load source context if available
            source_context = None
            if load_source and defn.get('file_path') and defn.get('line_number'):
                source_context = self.load_source_context(
                    defn['file_path'],
                    defn['line_number'],
                    context_lines=10
                )

            # Generate
            try:
                description = self.generate_description(name, defn, source_context)
                defn['description'] = description
                self.stats['generated_descriptions'] += 1
                print(f"    → {description[:80]}...")
            except Exception as e:
                print(f"    → Failed: {e}")
                defn['description'] = self._generate_fallback_description(name, defn)
                self.stats['failed_generations'] += 1

        # Save enriched index
        print()
        print("-" * 60)
        print(f"Saving enriched index to: {output_path}")

        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(index, f, indent=2, ensure_ascii=False)

        # Print statistics
        print()
        print("=" * 60)
        print("Enrichment Complete!")
        print("=" * 60)
        print(f"Total definitions:         {self.stats['total_definitions']}")
        print(f"Kept existing docstrings:  {self.stats['kept_docstrings']}")
        print(f"Generated descriptions:    {self.stats['generated_descriptions']}")
        print(f"Failed generations:        {self.stats['failed_generations']}")
        print()

        success_rate = (self.stats['kept_docstrings'] + self.stats['generated_descriptions']) / self.stats['total_definitions'] * 100
        print(f"Success rate: {success_rate:.1f}%")


def main():
    """Command-line interface for index enrichment."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Enrich Lean index with natural language descriptions'
    )
    parser.add_argument(
        '--input',
        type=str,
        default='agents/search/data/lean_index.json',
        help='Path to input index'
    )
    parser.add_argument(
        '--output',
        type=str,
        default='agents/search/data/enriched_lean_index.json',
        help='Path to output enriched index'
    )
    parser.add_argument(
        '--no-source',
        action='store_true',
        help='Do not load source code context'
    )
    parser.add_argument(
        '--model',
        type=str,
        default='gpt-4o-mini',
        help='OpenAI model to use'
    )
    parser.add_argument(
        '--no-skip-existing',
        action='store_true',
        help='Regenerate descriptions even if they already exist'
    )

    args = parser.parse_args()

    # Create enricher
    enricher = IndexEnricher(model=args.model)

    # Run enrichment
    enricher.enrich_index(
        index_path=Path(args.input),
        output_path=Path(args.output),
        load_source=not args.no_source,
        skip_existing=not args.no_skip_existing
    )


if __name__ == '__main__':
    main()
