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
from openai import OpenAI

# Get the project root directory (parent of scripts/)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)

OPENAI_MODEL = "gpt-5"
OPENAI_KEY_PATH = os.path.join(PROJECT_ROOT, "openai_key.txt")

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

# ------------------- OpenAI -------------------

def load_openai_client() -> OpenAI:
    """Load OpenAI client with API key from file or environment."""
    key = None
    if os.path.exists(OPENAI_KEY_PATH):
        with open(OPENAI_KEY_PATH, "r", encoding="utf-8") as f:
            key = f.read().strip()
    else:
        key = os.getenv("OPENAI_API_KEY")

    if not key:
        print("ERROR: No OpenAI API key found. Set OPENAI_API_KEY env var or create openai_key.txt",
              file=sys.stderr)
        sys.exit(1)

    return OpenAI(api_key=key)

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

def call_openai_fix(client: OpenAI, system_prompt: str, user_prompt: str) -> str:
    """Call OpenAI to get corrected code with retry logic."""
    import time

    max_retries = 3
    for attempt in range(max_retries):
        try:
            # Set a custom timeout
            client.timeout = 300.0  # 5 minutes

            resp = client.responses.create(
                model=OPENAI_MODEL,
                instructions=system_prompt,
                input=[{"role": "user", "content": [{"type": "input_text", "text": user_prompt}]}],
            )

            # Extract text from response
            if hasattr(resp, "output_text") and isinstance(resp.output_text, str):
                return resp.output_text
            if hasattr(resp, "output") and isinstance(resp.output, list):
                for item in resp.output:
                    content = getattr(item, "content", None)
                    if isinstance(content, list):
                        for seg in content:
                            text = getattr(seg, "text", None)
                            if isinstance(text, str):
                                return text
                    text2 = getattr(item, "text", None)
                    if isinstance(text2, str):
                        return text2
            raise RuntimeError("OpenAI: could not extract text from response")

        except Exception as e:
            if attempt < max_retries - 1:
                wait_time = (attempt + 1) * 2  # Exponential backoff: 2s, 4s, 6s
                print(f"[fix_tactic_file] API error (attempt {attempt+1}/{max_retries}): {e}")
                print(f"[fix_tactic_file] Retrying in {wait_time} seconds...")
                time.sleep(wait_time)
            else:
                print(f"[fix_tactic_file] API error after {max_retries} attempts: {e}")
                raise

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

    # Load OpenAI client and prompts
    client = load_openai_client()
    system_prompt = load_prompt("fix_tactic_system.txt")

    # Repair loop
    for iteration in range(1, args.max_iterations + 1):
        print(f"\n[fix_tactic_file] === Iteration {iteration}/{args.max_iterations} ===")

        # Build user prompt with current code and diagnostics
        user_prompt = build_user_prompt(lean_code, diags, treat_warn)

        # Call OpenAI
        print(f"[fix_tactic_file] Calling OpenAI ({OPENAI_MODEL})...")
        raw_response = call_openai_fix(client, system_prompt, user_prompt)
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
