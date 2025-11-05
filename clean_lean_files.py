#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
clean_lean_files.py

Recursively removes all comments and namespace declarations from Lean files.

Removes:
  - block comments: /-- ... -/, /-! ... -/, /- ... -/
  - line comments:  -- ...
  - namespace declarations: 'namespace X', 'end X'
  - duplicate 'open ...' lines (keeps only the first one)
  - 'TaskNNN.' prefixes inside '#guard ...' lines (e.g., 'Task863.findX' -> 'findX')

Usage:
    python clean_lean_files.py /path/to/folder
"""

import re
import sys
from pathlib import Path


def clean_lean_code(text: str) -> str:
    # --- Remove all block comments: /- ... -/ (including /-- and /-!)
    text = re.sub(r'/-(?:!|-)?[\s\S]*?-\s*/', '', text)

    # --- Remove all single-line comments starting with --
    text = re.sub(r'--.*', '', text)

    # --- Remove namespace and end lines
    text = re.sub(r'^\s*namespace\s+\S+\s*$', '', text, flags=re.MULTILINE)
    text = re.sub(r'^\s*end\s+\S+\s*$', '', text, flags=re.MULTILINE)

    # --- Keep only the first 'open ...' line, remove all others
    lines = text.splitlines()
    seen_open = False
    kept_lines = []
    for line in lines:
        if re.match(r'^\s*open\b', line):
            if seen_open:
                continue
            seen_open = True
        kept_lines.append(line)
    text = "\n".join(kept_lines)

    # --- On lines starting with '#guard', remove any 'Task<digits>.' prefixes
    def strip_task_in_guard(match: re.Match) -> str:
        line = match.group(0)
        # Remove occurrences like Task863., Task12., etc., anywhere in the guard line
        return re.sub(r'\bTask\d+\.', '', line)

    text = re.sub(r'(?m)^[ \t]*#guard.*$', strip_task_in_guard, text)

    # --- Collapse multiple empty lines
    text = re.sub(r'\n{3,}', '\n\n', text)

    # --- Trim leading/trailing whitespace and ensure final newline
    return text.strip() + '\n'


def process_file(path: Path):
    content = path.read_text(encoding='utf-8')
    cleaned = clean_lean_code(content)
    path.write_text(cleaned, encoding='utf-8')
    print(f"✔ Cleaned: {path}")


def main():
    if len(sys.argv) != 2:
        print("Usage: python clean_lean_files.py <folder>")
        sys.exit(1)

    folder = Path(sys.argv[1]).resolve()
    if not folder.is_dir():
        print(f"Error: {folder} is not a directory.")
        sys.exit(1)

    for lean_file in folder.rglob("*.lean"):
        process_file(lean_file)


if __name__ == "__main__":
    main()
