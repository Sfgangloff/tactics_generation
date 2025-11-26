#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fix_tactic_focused.py

Focused iterative repair: Extract specific functions with errors,
send only that function + errors to LLM, replace just that function.

Usage:
    python scripts/fix_tactic_focused.py TacticsGeneration/Tactics/propositions_4_1.lean
"""

import subprocess
import json
import os
import re
import sys
import traceback
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from claude_agent_sdk import query
import anyio

# Get the project root directory
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)

CLAUDE_MODEL = "claude-sonnet-4"  # Note: Claude Agent SDK may use its own default model

# ------------------- Project detection -------------------

def find_project_root(start: Path) -> Optional[Path]:
    """Find a Lake project root by walking upward."""
    cur = start.resolve()
    for p in [cur] + list(cur.parents):
        if (p / "lakefile.lean").exists() or (p / "lake-manifest.json").exists() or (p / "lakefile.toml").exists():
            return p
    return None

# ------------------- Lean runner -------------------

def run_lean_check(file_path: str) -> List[Dict]:
    """Run Lean and return diagnostics with line numbers."""
    file_abs = str(Path(file_path).resolve())
    proj_root = find_project_root(Path(file_abs).parent)

    cmd = ["lake", "env", "lean", file_abs]
    workdir = str(proj_root) if proj_root else None

    try:
        result = subprocess.run(
            cmd, cwd=workdir, capture_output=True, text=True, timeout=180
        )
    except subprocess.TimeoutExpired:
        return [{"kind": "error", "line": None, "message": "Lean compilation timed out"}]

    output_lines = ((result.stdout or "") + "\n" + (result.stderr or "")).splitlines()

    diags: List[Dict] = []
    for ln in output_lines:
        if ("error:" not in ln) and ("warning:" not in ln):
            continue

        # Parse: file:line:col: error: message
        parts = ln.split(":", 4)
        line_num = None
        if len(parts) >= 4 and parts[1].isdigit():
            try:
                line_num = int(parts[1])
            except ValueError:
                pass

        kind = None
        message = ln
        if "error:" in ln:
            kind = "error"
            idx = ln.find("error:")
            message = ln[idx + len("error:"):].strip()
        elif "warning:" in ln:
            kind = "warning"
            idx = ln.find("warning:")
            message = ln[idx + len("warning:"):].strip()

        if kind:
            diags.append({"kind": kind, "line": line_num, "message": message})

    return diags

# ------------------- Function extraction -------------------

def extract_function_at_line(file_content: str, line_num: int) -> Tuple[Optional[str], Optional[int], Optional[int]]:
    """
    Extract the function/theorem definition containing the given line.
    Returns (function_text, start_line, end_line) or (None, None, None).

    Looks for `def`, `theorem`, `lemma`, etc.
    """
    lines = file_content.splitlines()
    if line_num < 1 or line_num > len(lines):
        return None, None, None

    # Find definition start by going backwards
    def_start = None
    for i in range(line_num - 1, -1, -1):
        line = lines[i].strip()
        if re.match(r'^(private\s+)?(partial\s+)?(def|theorem|lemma|example)\s+', line):
            def_start = i
            break
        # Stop if we hit another top-level definition
        if i < line_num - 1 and re.match(r'^(private\s+)?(partial\s+)?(def|theorem|lemma|structure|class|inductive|example)\s+', line):
            break

    if def_start is None:
        return None, None, None

    # Find definition end by looking for next top-level definition
    # For theorems with tactics: check if it's `:= by` followed by tactic on next line(s)
    if ':=' in lines[def_start] and 'by' in lines[def_start]:
        # Check if there's a tactic body on the next line(s)
        def_indent = len(lines[def_start]) - len(lines[def_start].lstrip())
        def_end = def_start

        # Look for indented lines after `:= by`
        for i in range(def_start + 1, min(def_start + 10, len(lines))):  # Look ahead up to 10 lines
            if not lines[i].strip():
                continue
            curr_indent = len(lines[i]) - len(lines[i].lstrip())

            # If this line is more indented, it's part of the tactic body
            if curr_indent > def_indent:
                def_end = i
            else:
                # Hit a new definition or same-level line
                break

        # Extract the theorem + tactic body
        theorem_lines = lines[def_start:def_end + 1]
        return '\n'.join(theorem_lines), def_start + 1, def_end + 1

    # Multi-line: find end by indentation
    def_indent = len(lines[def_start]) - len(lines[def_start].lstrip())
    def_end = len(lines) - 1

    for i in range(def_start + 1, len(lines)):
        line = lines[i]
        if not line.strip():
            continue
        curr_indent = len(line) - len(line.lstrip())

        # If we hit another top-level def at same or less indentation, stop
        if curr_indent <= def_indent and re.match(r'^\s*(private\s+)?(partial\s+)?(def|theorem|lemma|example|/--)\s+', line):
            def_end = i - 1
            break

    # Extract text
    def_lines = lines[def_start:def_end + 1]
    def_text = '\n'.join(def_lines)

    return def_text, def_start + 1, def_end + 1  # Convert to 1-indexed

# ------------------- Claude Agent SDK -------------------
# Note: Claude Agent SDK handles authentication automatically via environment variables

def build_focused_prompt(func_text: str, errors: List[Dict], failing_tests: List = None) -> str:
    """Build a focused prompt with the function and its errors or failing tests."""
    prompt = f"# Lean code to fix:\n```lean\n{func_text}\n```\n\n"

    # If we have failing tests, show them
    if failing_tests:
        prompt += f"# Failing test theorems ({len(failing_tests)} total):\n"
        prompt += "The following theorems are VALID TAUTOLOGIES that should be provable,\n"
        prompt += "but they fail with the current tactic implementation:\n\n"
        for i, (test_text, err) in enumerate(failing_tests[:5], 1):  # Show first 5
            prompt += f"## Test {i}:\n```lean\n{test_text}\n```\n"
            prompt += f"Error: {err['message'][:150]}\n\n"

        prompt += "\nPlease improve the tactic implementation to handle these cases.\n"
        prompt += "The tactic should be able to prove these tautologies constructively.\n"
    else:
        # Regular errors
        prompt += f"# Compilation errors:\n"
        for i, err in enumerate(errors[:10], 1):
            line_info = f"line {err['line']}" if err['line'] else "unknown line"
            prompt += f"{i}. [{err['kind']}] {line_info}: {err['message'][:200]}\n"

        prompt += "\nPlease fix this code to resolve the errors.\n"

    prompt += "Return ONLY the corrected code, nothing else."

    return prompt

async def call_claude_fix_async(func_text: str, errors: List[Dict], failing_tests: List = None) -> str:
    """Async call to Claude Agent SDK to fix the specific function/theorem."""
    system_prompt = """You are an expert Lean 4 metaprogramming assistant.
Fix the given Lean code (function, theorem, or tactic) to resolve compilation errors.

Common fixes:
- Replace `Array.get! idx` with `arr[idx]` when you have a hypothesis `h : idx < arr.size` in scope
- For tactic implementations: if test theorems fail with "not constructively inhabitable",
  the tactic is incomplete. Improve the tactic logic to handle those cases.
- Common tactic patterns to add:
  * Check if goal matches a local hypothesis
  * Try applying locals and recursively closing subgoals
  * Add more pattern matching for specific propositional structures
  * Consider using `classical` reasoning when needed
- Ensure all array accesses have proper bounds proofs

Return ONLY the corrected code, maintaining the same structure (theorem/def/etc)."""

    user_prompt = build_focused_prompt(func_text, errors, failing_tests)

    # Combine system and user prompts
    full_prompt = f"{system_prompt}\n\n{user_prompt}"

    # Collect response from streaming API
    response_text = ""
    async for message in query(prompt=full_prompt):
        response_text += str(message)

    if not response_text:
        raise RuntimeError("Claude Agent SDK: no response content")

    return response_text

def call_claude_fix(func_text: str, errors: List[Dict], failing_tests: List = None) -> str:
    """Synchronous wrapper for async Claude call."""
    return anyio.run(call_claude_fix_async, func_text, errors, failing_tests)

def normalize_code(s: str) -> str:
    """Remove markdown fences if present."""
    lines = s.split('\n')
    cleaned = []
    in_fence = False

    for line in lines:
        if re.match(r'^\s*```', line):
            in_fence = not in_fence
            continue
        cleaned.append(line)

    return '\n'.join(cleaned).strip()

# ------------------- Main -------------------

def main():
    import argparse
    ap = argparse.ArgumentParser(description="Focused repair of Lean tactic files")
    ap.add_argument("lean_file", help="Path to the Lean file")
    ap.add_argument("--max-iterations", type=int, default=5)
    args = ap.parse_args()

    lean_path = args.lean_file
    if not os.path.exists(lean_path):
        print(f"ERROR: File not found: {lean_path}", file=sys.stderr)
        sys.exit(1)

    for iteration in range(1, args.max_iterations + 1):
        print(f"\n[focused_fix] === Iteration {iteration}/{args.max_iterations} ===")

        # Check current errors
        diags = run_lean_check(lean_path)
        errors = [d for d in diags if d["kind"] == "error"]

        if not errors:
            print("[focused_fix] ✓ No errors! File compiles successfully.")
            return

        print(f"[focused_fix] Found {len(errors)} error(s).")

        # Read file once
        with open(lean_path, "r", encoding="utf-8") as f:
            file_content = f.read()

        # Categorize errors: tactic implementation vs test theorems
        tactic_errors = []
        test_errors = []
        failing_tests = []

        for err in errors:
            if err["line"] is None:
                continue

            # Try to extract the function/theorem
            f_text, s_line, e_line = extract_function_at_line(file_content, err["line"])
            if f_text is None:
                continue

            # Check if this is a run_tac test theorem
            if 'run_tac' in f_text and f_text.strip().startswith('theorem'):
                test_errors.append(err)
                failing_tests.append((f_text, err))
            else:
                tactic_errors.append((err, f_text, s_line, e_line))

        # Strategy 1: Fix tactic implementation errors first
        if tactic_errors:
            target_error, func_text, start_line, end_line = tactic_errors[0]
            print(f"[focused_fix] Targeting tactic implementation error at line {target_error['line']}")
            print(f"[focused_fix] {target_error['message'][:100]}...")
            print(f"[focused_fix] Extracted from lines {start_line}-{end_line} ({end_line - start_line + 1} lines)")

        # Strategy 2: If only test errors, fix the tactic to handle failing tests
        elif test_errors:
            print(f"[focused_fix] Found {len(test_errors)} failing test theorem(s).")
            print(f"[focused_fix] These are tautologies that the tactic should prove.")
            print(f"[focused_fix] Will improve the tactic implementation to handle them.")

            # Find the tactic definition (intro_all_then_assumption)
            tactic_pattern = r'def\s+intro_all_then_assumption\s*:'
            tactic_match = re.search(tactic_pattern, file_content, re.MULTILINE)
            if not tactic_match:
                print("[focused_fix] Could not find tactic definition 'intro_all_then_assumption'")
                sys.exit(1)

            tactic_line = file_content[:tactic_match.start()].count('\n') + 1
            func_text, start_line, end_line = extract_function_at_line(file_content, tactic_line)

            if func_text is None:
                print("[focused_fix] Could not extract tactic definition")
                sys.exit(1)

            print(f"[focused_fix] Extracted tactic from lines {start_line}-{end_line} ({end_line - start_line + 1} lines)")
            target_error = test_errors[0]  # Use first test error for context

        else:
            print("[focused_fix] No fixable errors found.")
            sys.exit(1)

        # Get all errors in this function's range
        func_errors = [e for e in errors if start_line <= (e["line"] or 0) <= end_line]
        print(f"[focused_fix] Function has {len(func_errors)} error(s)")

        # Call Claude Agent SDK to fix
        print(f"[focused_fix] Calling Claude Agent SDK...")
        try:
            # If we have test errors, pass failing tests to guide the fix
            if test_errors and not tactic_errors:
                fixed_func = call_claude_fix(func_text, func_errors, failing_tests)
            else:
                fixed_func = call_claude_fix(func_text, func_errors)
            fixed_func = normalize_code(fixed_func)
        except Exception as e:
            print(f"[focused_fix] API error: {e}")
            print("[focused_fix] Full traceback:")
            traceback.print_exc()
            sys.exit(1)

        # Replace function in file
        lines = file_content.splitlines()
        new_lines = lines[:start_line - 1] + fixed_func.splitlines() + lines[end_line:]
        new_content = '\n'.join(new_lines)

        # Check if identical
        if new_content.strip() == file_content.strip():
            print("[focused_fix] ⚠ No changes made by LLM")
            continue

        # Write back
        with open(lean_path, "w", encoding="utf-8") as f:
            f.write(new_content)

        print(f"[focused_fix] Replaced function. Re-checking...")

    # Final check
    diags = run_lean_check(lean_path)
    errors = [d for d in diags if d["kind"] == "error"]
    if not errors:
        print("[focused_fix] ✓ Success! File compiles.")
    else:
        print(f"[focused_fix] ✗ Still {len(errors)} error(s) after {args.max_iterations} iterations.")
        sys.exit(1)

if __name__ == "__main__":
    main()
