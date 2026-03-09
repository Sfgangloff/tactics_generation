#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
re_json.py

Usage:
    python re_json.py input.jsonl /path/to/Validated output.jsonl

For each JSON object (line) in input.jsonl, this script:
- reads the Lean file Validated/Task{task_id}.lean,
- sets "code" to that file's content,
- sets "test_list" to all '#guard ...' lines from that file,
- keeps only "text", "task_id", "code", "test_list",
- writes the result as a line to output.jsonl.
"""

import sys
import json
import re
from pathlib import Path

def extract_tests_from_lean(lean_text: str) -> list[str]:
    # Collect lines that start (possibly after spaces) with '#guard'
    tests = []
    for line in lean_text.splitlines():
        if re.match(r'^\s*#guard\b', line):
            tests.append(line.strip())
    return tests

def main():
    if len(sys.argv) != 4:
        print("Usage: python transform_jsonl_with_lean.py input.jsonl /path/to/Validated output.jsonl")
        sys.exit(1)

    input_path = Path(sys.argv[1])
    validated_dir = Path(sys.argv[2])
    output_path = Path(sys.argv[3])

    if not input_path.is_file():
        print(f"Error: {input_path} is not a file.", file=sys.stderr)
        sys.exit(1)
    if not validated_dir.is_dir():
        print(f"Error: {validated_dir} is not a directory.", file=sys.stderr)
        sys.exit(1)

    with input_path.open('r', encoding='utf-8') as fin, \
         output_path.open('w', encoding='utf-8') as fout:
        for lineno, line in enumerate(fin, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError as e:
                print(f"[warn] Skipping line {lineno}: JSON decode error: {e}", file=sys.stderr)
                continue

            # Require task_id and text
            if "task_id" not in obj or "text" not in obj:
                print(f"[warn] Skipping line {lineno}: missing 'task_id' or 'text'", file=sys.stderr)
                continue

            task_id = obj["task_id"]
            lean_file = validated_dir / f"Task{task_id}.lean"
            if not lean_file.is_file():
                print(f"[warn] Skipping task_id={task_id} (line {lineno}): {lean_file} not found", file=sys.stderr)
                continue

            lean_text = lean_file.read_text(encoding='utf-8')
            # Normalize newlines to '\n' (optional but cleaner for JSON)
            lean_text = lean_text.replace('\r\n', '\n').replace('\r', '\n')

            tests = extract_tests_from_lean(lean_text)

            out_obj = {
                "text": obj["text"],
                "task_id": task_id,
                "code": lean_text,
                "test_list": tests,
            }
            fout.write(json.dumps(out_obj, ensure_ascii=False) + "\n")

if __name__ == "__main__":
    main()
