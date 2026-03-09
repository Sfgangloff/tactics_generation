#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fix_tactic_file.py

Iteratively repair Lean tactic files by:
1. Running the file through Lean to get compilation errors
2. Sending the file + errors to OpenAI
3. Getting back a corrected version
4. Testing again with bounded iterations

Usage:
    python scripts/fix_tactic_file.py TacticsGeneration/Tactics/propositions_4_1.lean

    # With custom max iterations (default: 5)
    python scripts/fix_tactic_file.py --max-iterations 10 TacticsGeneration/Tactics/propositions_4_1.lean

    # Allow warnings (only fix errors)
    python scripts/fix_tactic_file.py --allow-warnings TacticsGeneration/Tactics/propositions_4_1.lean
"""

import subprocess
import json
import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Optional
from claude_agent_sdk import query
import anyio

# Get the project root directory (parent of scripts/)
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

def run_lean_check(file_path: str, treat_warnings_as_errors: bool) -> List[Dict]:
    """
    Run Lean (prefer 'lake env lean') and return a list of diagnostics:
      [{'kind': 'error'|'warning', 'line': Optional[int], 'message': str}, ...]
    """
    file_abs = str(Path(file_path).resolve())
    proj_root = find_project_root(Path(file_abs).parent)

    # Base command prefers lake
    cmd = ["lake", "env", "lean"]
    workdir = str(proj_root) if proj_root else None

    if treat_warnings_as_errors:
        cmd += ["-DwarningAsError=true"]

    cmd += [file_abs]

    try:
        result = subprocess.run(
            cmd, cwd=workdir, capture_output=True, text=True, timeout=300
        )
    except FileNotFoundError:
        print(f"[fix_tactic_file] Command 'lake' not found. Ensure Lake is on PATH.")
        sys.exit(1)
    except subprocess.TimeoutExpired:
        print(f"[fix_tactic_file] Lean check timed out after 300 seconds.")
        return [{"kind": "error", "line": None, "message": "Lean compilation timed out"}]

    # Scan BOTH stdout and stderr
    output_lines = ((result.stdout or "") + "\n" + (result.stderr or "")).splitlines()

    diags: List[Dict] = []
    for ln in output_lines:
        if ("error:" not in ln) and ("warning:" not in ln):
            continue
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

# ------------------- Claude Agent SDK -------------------
# Note: Claude Agent SDK handles authentication automatically via environment variables

def load_prompt(filename: str) -> str:
    """Load a prompt template from the prompts/ directory."""
    try:
        with open(os.path.join(PROJECT_ROOT, "prompts", filename), "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        print(f"ERROR: Could not find prompt file: prompts/{filename}", file=sys.stderr)
        sys.exit(1)

def build_user_prompt(lean_code: str, diags: List[Dict], treat_warnings_as_errors: bool, max_diags: int = 30) -> str:
    """Build the user prompt with file content and diagnostics."""
    # Limit diagnostics to avoid overwhelming the API
    limited_diags = diags[:max_diags]
    total_count = len(diags)

    summary = {
        "treat_warnings_as_errors": treat_warnings_as_errors,
        "diagnostics": limited_diags,
        "total_diagnostics": total_count,
        "showing_first": len(limited_diags)
    }

    prompt = f"# Current Lean file content:\n```lean\n{lean_code}\n```\n\n"
    prompt += f"# Lean diagnostics (showing first {len(limited_diags)} of {total_count} total):\n```json\n{json.dumps(summary, indent=2)}\n```\n\n"
    prompt += "Please provide the corrected Lean file that fixes all the errors (and warnings if treat_warnings_as_errors is true). "
    prompt += "Focus on fixing the errors shown above - they are the first ones encountered by the compiler.\n"
    prompt += "Return ONLY the complete corrected Lean code, nothing else."

    return prompt

async def call_claude_fix_async(system_prompt: str, user_prompt: str) -> str:
    """Async call to Claude Agent SDK with retry logic."""
    import time

    max_retries = 3
    for attempt in range(max_retries):
        try:
            # Combine system and user prompts
            full_prompt = f"{system_prompt}\n\n{user_prompt}"

            # Collect response from streaming API with timeout
            response_text = ""
            async with anyio.fail_after(300.0):  # 5 minutes timeout
                async for message in query(prompt=full_prompt):
                    response_text += str(message)

            if not response_text:
                raise RuntimeError("Claude Agent SDK: empty response")

            return response_text

        except TimeoutError:
            if attempt < max_retries - 1:
                wait_time = (attempt + 1) * 2  # Exponential backoff: 2s, 4s, 6s
                print(f"[fix_tactic_file] Timeout (attempt {attempt+1}/{max_retries})")
                print(f"[fix_tactic_file] Retrying in {wait_time} seconds...")
                time.sleep(wait_time)
            else:
                print(f"[fix_tactic_file] Timeout after {max_retries} attempts")
                raise
        except Exception as e:
            if attempt < max_retries - 1:
                wait_time = (attempt + 1) * 2  # Exponential backoff: 2s, 4s, 6s
                print(f"[fix_tactic_file] API error (attempt {attempt+1}/{max_retries}): {e}")
                print(f"[fix_tactic_file] Retrying in {wait_time} seconds...")
                time.sleep(wait_time)
            else:
                print(f"[fix_tactic_file] API error after {max_retries} attempts: {e}")
                raise

def call_claude_fix(system_prompt: str, user_prompt: str) -> str:
    """Synchronous wrapper for async Claude call."""
    return anyio.run(call_claude_fix_async, system_prompt, user_prompt)

# ------------------- Output normalizer -------------------

FENCE_RE = re.compile(r"^\s*```(?:lean)?\s*|\s*```\s*$", re.IGNORECASE | re.MULTILINE)

def normalize_lean_source(s: str) -> str:
    """
    Strip code fences if present and clean up the output.
    """
    if not s:
        return s

    # Remove markdown code fences
    lines = s.split('\n')
    cleaned_lines = []
    in_code_block = False

    for line in lines:
        # Check if this line is a fence
        if re.match(r'^\s*```', line):
            in_code_block = not in_code_block
            continue
        cleaned_lines.append(line)

    result = '\n'.join(cleaned_lines).strip()
    return result

# ------------------- Main -------------------

def main():
    import argparse
    ap = argparse.ArgumentParser(
        description="Iteratively repair Lean tactic files using OpenAI"
    )
    ap.add_argument("lean_file", help="Path to the Lean tactic file to repair")
    ap.add_argument("--max-iterations", type=int, default=5,
                   help="Maximum number of repair iterations (default: 5)")
    ap.add_argument("--allow-warnings", action="store_true",
                   help="Only fix errors, allow warnings to remain")
    ap.add_argument("--treat-warnings-as-errors", action="store_true",
                   help="Treat warnings as errors (default: False)")
    args = ap.parse_args()

    lean_path = args.lean_file

    if not os.path.exists(lean_path):
        print(f"ERROR: File not found: {lean_path}", file=sys.stderr)
        sys.exit(1)

    # Determine warning treatment
    treat_warn = args.treat_warnings_as_errors and not args.allow_warnings

    # Read initial file
    with open(lean_path, "r", encoding="utf-8") as f:
        lean_code = f.read()

    print(f"[fix_tactic_file] Checking: {lean_path}")

    # Initial check
    diags = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
    blocking = [d for d in diags if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

    if not blocking:
        if diags:
            print(f"[fix_tactic_file] ✓ File compiles successfully. {len(diags)} non-blocking warning(s) present.")
        else:
            print("[fix_tactic_file] ✓ File compiles cleanly (no errors, no warnings).")
        return

    print(f"[fix_tactic_file] Found {len(blocking)} blocking diagnostic(s).")
    print(f"[fix_tactic_file] Starting repair with max {args.max_iterations} iteration(s)...")

    # Load prompts
    system_prompt = load_prompt("fix_tactic_system.txt")

    # Repair loop
    for iteration in range(1, args.max_iterations + 1):
        print(f"\n[fix_tactic_file] === Iteration {iteration}/{args.max_iterations} ===")

        # Build user prompt with current code and diagnostics
        user_prompt = build_user_prompt(lean_code, diags, treat_warn)

        # Call Claude Agent SDK
        print(f"[fix_tactic_file] Calling Claude Agent SDK...")
        raw_response = call_claude_fix(system_prompt, user_prompt)
        candidate = normalize_lean_source(raw_response)

        # Check if code is identical
        if candidate.strip() == lean_code.strip():
            print("[fix_tactic_file] ⚠ Model returned identical code. Adding stricter instructions...")
            system_prompt += "\n\nIMPORTANT: The previous attempt returned unchanged code. You MUST make changes to fix the errors. Do not return the same code again."
            continue

        # Write candidate to file
        with open(lean_path, "w", encoding="utf-8") as f:
            f.write(candidate)

        print(f"[fix_tactic_file] Wrote candidate code. Checking with Lean...")

        # Re-check
        diags = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
        blocking = [d for d in diags if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

        if not blocking:
            if diags:
                print(f"[fix_tactic_file] ✓ Success! File now compiles. {len(diags)} non-blocking warning(s) remain.")
            else:
                print("[fix_tactic_file] ✓ Success! File compiles cleanly (no errors, no warnings).")
            return

        print(f"[fix_tactic_file] Still {len(blocking)} blocking diagnostic(s) remaining.")

        # Show first few errors for debugging
        for i, d in enumerate(blocking[:3], 1):
            where = f"line {d['line']}" if d['line'] is not None else "line ?"
            print(f"  {i}. [{d['kind']}] {where}: {d['message'][:100]}...")

        # Update for next iteration
        lean_code = candidate

    # If we get here, we've exhausted all iterations
    print(f"\n[fix_tactic_file] ✗ Failed to repair after {args.max_iterations} iteration(s).")
    print(f"[fix_tactic_file] Final status: {len(blocking)} blocking diagnostic(s):")
    for i, d in enumerate(blocking[:5], 1):
        where = f"line {d['line']}" if d['line'] is not None else "line ?"
        print(f"  {i}. [{d['kind']}] {where}: {d['message'][:150]}...")

    sys.exit(1)

if __name__ == "__main__":
    main()
