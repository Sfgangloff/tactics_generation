#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
lean_indexer.py

Scans Lean 4 source files and builds a searchable index of definitions.
"""

import re
import json
from pathlib import Path
from typing import List, Dict, Optional, Set
import subprocess


class LeanIndexer:
    """
    Builds a searchable index of Lean 4 definitions from source files.

    Extracts:
    - Function definitions (def)
    - Theorem definitions (theorem)
    - Structure definitions (structure)
    - Class definitions (class)
    - Inductive type definitions (inductive)
    - Type signatures
    - Doc comments
    """

    # Regex patterns for Lean definitions
    PATTERNS = {
        'def': re.compile(
            r'^\s*(?:protected\s+)?(?:private\s+)?def\s+(\w+(?:\.\w+)*)'
            r'(?:\s*\(.*?\))?\s*:\s*([^\n:=]+?)(?:$|:=)',
            re.MULTILINE
        ),
        'theorem': re.compile(
            r'^\s*(?:protected\s+)?(?:private\s+)?theorem\s+(\w+(?:\.\w+)*)'
            r'(?:\s*\(.*?\))?\s*:\s*([^\n:=]+?)(?:$|:=)',
            re.MULTILINE
        ),
        'lemma': re.compile(
            r'^\s*(?:protected\s+)?(?:private\s+)?lemma\s+(\w+(?:\.\w+)*)'
            r'(?:\s*\(.*?\))?\s*:\s*([^\n:=]+?)(?:$|:=)',
            re.MULTILINE
        ),
        'structure': re.compile(
            r'^\s*(?:protected\s+)?structure\s+(\w+(?:\.\w+)*)'
            r'(?:\s+extends\s+[^\n{]+)?',
            re.MULTILINE
        ),
        'class': re.compile(
            r'^\s*(?:protected\s+)?class\s+(\w+(?:\.\w+)*)'
            r'(?:\s+extends\s+[^\n{]+)?',
            re.MULTILINE
        ),
        'inductive': re.compile(
            r'^\s*(?:protected\s+)?inductive\s+(\w+(?:\.\w+)*)'
            r'(?:\s*\(.*?\))?\s*(?::\s*([^\n|]+?))?(?:$|\||where)',
            re.MULTILINE
        ),
        'abbrev': re.compile(
            r'^\s*(?:protected\s+)?abbrev\s+(\w+(?:\.\w+)*)'
            r'\s*:=',
            re.MULTILINE
        ),
    }

    # Pattern for doc comments
    DOC_COMMENT_PATTERN = re.compile(
        r'/--\s*(.*?)\s*-/',
        re.DOTALL
    )

    # Pattern for module doc comments
    MODULE_DOC_PATTERN = re.compile(
        r'/-!\s*(.*?)\s*-/',
        re.DOTALL
    )

    def __init__(self):
        """Initialize the indexer."""
        self.index: Dict[str, Dict] = {}
        self.lean_root: Optional[Path] = None

    def find_lean_root(self) -> Optional[Path]:
        """
        Find the Lean installation root directory.

        Returns:
            Path to Lean root, or None if not found
        """
        try:
            # Try to get elan default toolchain
            result = subprocess.run(
                ['elan', 'show'],
                capture_output=True,
                text=True,
                timeout=5
            )

            if result.returncode == 0:
                # Parse output to find toolchain path
                for line in result.stdout.splitlines():
                    if 'default toolchain' in line.lower() or 'stable' in line:
                        # Extract version
                        match = re.search(r'(leanprover/lean4:[^\s]+|stable[^\s]*)', line)
                        if match:
                            version = match.group(1).replace('leanprover/lean4:', '')

                            # Find elan toolchains directory
                            home = Path.home()
                            elan_dir = home / '.elan' / 'toolchains'

                            # Look for matching toolchain
                            for toolchain_dir in elan_dir.glob('*'):
                                if version in toolchain_dir.name or 'stable' in toolchain_dir.name:
                                    lean_lib = toolchain_dir / 'lib' / 'lean' / 'library'
                                    if lean_lib.exists():
                                        self.lean_root = toolchain_dir
                                        return self.lean_root
        except (subprocess.TimeoutExpired, FileNotFoundError):
            pass

        # Fallback: try common locations
        possible_roots = [
            Path.home() / '.elan' / 'toolchains',
            Path('/usr/local/lib/lean'),
            Path('/opt/lean'),
        ]

        for root in possible_roots:
            if root.exists():
                for toolchain in root.glob('*'):
                    lean_lib = toolchain / 'lib' / 'lean' / 'library'
                    if lean_lib.exists():
                        self.lean_root = toolchain
                        return self.lean_root

        return None

    def get_lean_version(self) -> str:
        """
        Get the current Lean version.

        Returns:
            Version string, or "unknown" if not found
        """
        try:
            result = subprocess.run(
                ['lean', '--version'],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                # Parse version from output
                match = re.search(r'version\s+([^\s,]+)', result.stdout)
                if match:
                    return match.group(1)
        except (subprocess.TimeoutExpired, FileNotFoundError):
            pass

        return "unknown"

    def find_source_directories(self, project_root: Path) -> Dict[str, Path]:
        """
        Find Lean source directories to index.

        Args:
            project_root: Root directory of the project

        Returns:
            Dict mapping source names to their paths
        """
        sources = {}

        # Core library
        if self.lean_root:
            core_lib = self.lean_root / 'lib' / 'lean' / 'library'
            if core_lib.exists():
                sources['core'] = core_lib

        # Lake packages (try both old and new locations)
        lake_packages_dirs = [
            project_root / '.lake' / 'packages',  # New Lake format
            project_root / 'lake-packages'         # Old Lake format
        ]

        for lake_packages in lake_packages_dirs:
            if not lake_packages.exists():
                continue

            # Batteries (includes Std in v4)
            batteries = lake_packages / 'batteries' / 'Batteries'
            if batteries.exists() and 'batteries' not in sources:
                sources['batteries'] = batteries

            # Std (standalone, if exists)
            std = lake_packages / 'std' / 'Std'
            if std.exists() and 'std' not in sources:
                sources['std'] = std

            # Mathlib (optional, might be large)
            mathlib = lake_packages / 'mathlib' / 'Mathlib'
            if mathlib.exists() and 'mathlib' not in sources:
                sources['mathlib'] = mathlib

        # Local project
        tactics_gen = project_root / 'TacticsGeneration'
        if tactics_gen.exists():
            sources['local'] = tactics_gen

        return sources

    def extract_doc_comment(self, content: str, pos: int) -> Optional[str]:
        """
        Extract doc comment immediately before a definition.

        Args:
            content: File content
            pos: Position of the definition

        Returns:
            Doc comment text, or None if not found
        """
        # Look backwards from position for doc comment
        before_def = content[:pos]

        # Find the last doc comment before the definition
        matches = list(self.DOC_COMMENT_PATTERN.finditer(before_def))
        if matches:
            last_match = matches[-1]
            # Check if the comment is close to the definition (within 100 chars)
            if pos - last_match.end() < 100:
                # Clean up the comment text
                doc_text = last_match.group(1)
                doc_text = re.sub(r'\s+', ' ', doc_text).strip()
                return doc_text

        return None

    def parse_lean_file(
        self,
        file_path: Path,
        source_name: str
    ) -> List[Dict]:
        """
        Parse a single Lean file and extract definitions.

        Args:
            file_path: Path to the .lean file
            source_name: Name of the source (e.g., 'batteries', 'std')

        Returns:
            List of definition dictionaries
        """
        try:
            content = file_path.read_text(encoding='utf-8')
        except (UnicodeDecodeError, FileNotFoundError) as e:
            print(f"Warning: Could not read {file_path}: {e}")
            return []

        definitions = []

        for def_type, pattern in self.PATTERNS.items():
            for match in pattern.finditer(content):
                name = match.group(1)

                # Extract type signature if available
                signature = None
                if len(match.groups()) > 1 and match.group(2):
                    sig_text = match.group(2).strip()
                    # Clean up signature
                    sig_text = re.sub(r'\s+', ' ', sig_text)
                    signature = f"{name} : {sig_text}"
                else:
                    # For definitions without explicit type, use simple format
                    signature = f"{name}"

                # Extract doc comment
                doc_comment = self.extract_doc_comment(content, match.start())

                # Calculate line number
                line_num = content[:match.start()].count('\n') + 1

                definitions.append({
                    'name': name,
                    'type': def_type,
                    'signature': signature,
                    'docstring': doc_comment,
                    'file_path': str(file_path.relative_to(file_path.parents[len(file_path.parents)-1])),
                    'line_number': line_num,
                    'source': source_name
                })

        return definitions

    def build_index(
        self,
        project_root: Path,
        sources: Optional[List[str]] = None,
        verbose: bool = False
    ) -> Dict[str, Dict]:
        """
        Build the index by scanning Lean source files.

        Args:
            project_root: Root directory of the project
            sources: List of source names to index (None = all)
            verbose: Print progress messages

        Returns:
            Dictionary mapping definition names to their metadata
        """
        if verbose:
            print("Finding Lean installation...")

        self.find_lean_root()

        if verbose:
            print(f"Lean root: {self.lean_root}")
            print("Finding source directories...")

        source_dirs = self.find_source_directories(project_root)

        if verbose:
            print(f"Found sources: {list(source_dirs.keys())}")

        # Filter sources if specified
        if sources:
            source_dirs = {k: v for k, v in source_dirs.items() if k in sources}

        total_files = 0
        total_definitions = 0

        for source_name, source_path in source_dirs.items():
            if verbose:
                print(f"\nIndexing {source_name} from {source_path}...")

            # Find all .lean files
            lean_files = list(source_path.rglob('*.lean'))
            total_files += len(lean_files)

            if verbose:
                print(f"  Found {len(lean_files)} .lean files")

            for lean_file in lean_files:
                definitions = self.parse_lean_file(lean_file, source_name)

                for defn in definitions:
                    # Use full qualified name as key
                    key = defn['name']

                    # Avoid duplicates (keep first occurrence)
                    if key not in self.index:
                        self.index[key] = defn
                        total_definitions += 1

        if verbose:
            print(f"\n{'='*60}")
            print(f"Indexing complete!")
            print(f"  Total files scanned: {total_files}")
            print(f"  Total definitions indexed: {total_definitions}")
            print(f"{'='*60}")

        return self.index

    def save_index(self, output_path: Path):
        """
        Save the index to a JSON file.

        Args:
            output_path: Path to save the index
        """
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.index, f, indent=2, ensure_ascii=False)

        print(f"Index saved to {output_path}")

    def load_index(self, index_path: Path) -> Dict[str, Dict]:
        """
        Load a previously built index from JSON.

        Args:
            index_path: Path to the index file

        Returns:
            The loaded index
        """
        with open(index_path, 'r', encoding='utf-8') as f:
            self.index = json.load(f)

        return self.index


def main():
    """Command-line interface for building the index."""
    import argparse

    parser = argparse.ArgumentParser(description='Build Lean code index')
    parser.add_argument(
        '--project-root',
        type=Path,
        default=Path.cwd(),
        help='Root directory of the project'
    )
    parser.add_argument(
        '--output',
        type=Path,
        default=Path('agents/search/data/lean_index.json'),
        help='Output path for the index'
    )
    parser.add_argument(
        '--sources',
        nargs='+',
        choices=['core', 'batteries', 'std', 'mathlib', 'local'],
        help='Sources to index (default: all except mathlib)'
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help='Print progress messages'
    )

    args = parser.parse_args()

    # Default sources (batteries only - includes Std functionality)
    if not args.sources:
        args.sources = ['batteries']

    print("Building Lean code index...")
    print(f"Project root: {args.project_root}")
    print(f"Sources: {args.sources}")
    print()

    indexer = LeanIndexer()
    indexer.build_index(
        project_root=args.project_root,
        sources=args.sources,
        verbose=args.verbose
    )

    indexer.save_index(args.output)

    # Print some statistics
    if indexer.index:
        print(f"\nIndex statistics:")
        by_type = {}
        by_source = {}

        for name, defn in indexer.index.items():
            def_type = defn.get('type', 'unknown')
            source = defn.get('source', 'unknown')

            by_type[def_type] = by_type.get(def_type, 0) + 1
            by_source[source] = by_source.get(source, 0) + 1

        print(f"  By type: {dict(sorted(by_type.items()))}")
        print(f"  By source: {dict(sorted(by_source.items()))}")


if __name__ == '__main__':
    main()
