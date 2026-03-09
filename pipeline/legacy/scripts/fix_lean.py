#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fix_lean.py

Run Lean (via Lake if present). If there are *any* diagnostics (errors or, by
default, warnings), look up the Python reference code by task_id from a JSONL
dataset, ask Claude Agent SDK to repair the Lean file (eliminating errors AND warnings),
then rewrite the file in place.

Usage:
    # For functional style:
    python fix_lean.py TacticsGeneration/Tasks/Functional/Task11.lean data/mblp-temp_functional.jsonl

    # For imperative style:
    python fix_lean.py TacticsGeneration/Tasks/Imperative/Task11.lean data/mblp-temp_imperative.jsonl

    # For free code style (no Python reference):
    python fix_lean.py TacticsGeneration/Tasks/Free_code/Task11.lean data/mblp-temp_free_code.jsonl

    # Optional flags:
    python fix_lean.py --allow-warnings TacticsGeneration/Tasks/Task11.lean data/mblp-temp_functional.jsonl
"""

import subprocess
import json
import os
import re
import sys
import shutil
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
        if (p / "lakefile.lean").exists() or (p / "lake-manifest.json").exists():
            return p
    return None

# ------------------- Lean runner -------------------

def run_lean_check(file_path: str, treat_warnings_as_errors: bool) -> List[Dict]:
    """
    Run Lean (prefer 'lake env lean') and return a list of diagnostics:
      [{'kind': 'error'|'warning', 'line': Optional[int], 'message': str}, ...]

    If treat_warnings_as_errors is True, we pass -DwarningAsError=true so Lean itself
    fails on warnings; we still parse for clarity.
    """
    file_abs = str(Path(file_path).resolve())
    proj_root = find_project_root(Path(file_abs).parent)

    # Base command prefers lake
    if proj_root is not None and shutil.which("lake"):
        cmd = ["lake", "env", "lean"]
        workdir = str(proj_root)
        used = "lake env lean"
    else:
        cmd = ["lean"]
        workdir = None
        used = "lean"

    if treat_warnings_as_errors:
        cmd += ["-DwarningAsError=true"]

    cmd += [file_abs]

    try:
        result = subprocess.run(
            cmd, cwd=workdir, capture_output=True, text=True, timeout=120
        )
    except FileNotFoundError:
        print(f"[fix_lean] Command not found while invoking {used!r}. Ensure Lean/Lake are on PATH.")
        sys.exit(1)

    # Scan BOTH stdout and stderr; Lean sometimes returns 0 with diagnostics.
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
                line_num = None
        msg = parts[-1].strip()
        kind = "error" if "error:" in ln else "warning"
        diags.append({"kind": kind, "line": line_num, "message": msg})

    # Helpful hint if Batteries import failed while not using lake
    if any("unknown module prefix 'Batteries'" in d["message"] for d in diags):
        if used == "lean":
            print(
                "[fix_lean] HINT: 'import Batteries' requires a Lake project with the 'batteries' dependency.\n"
                "          The script will use 'lake env lean' automatically if run under a Lake project."
            )
    return diags

# ------------------- Dataset helpers -------------------

def extract_task_id(lean_path: str) -> int:
    m = re.search(r"[Tt]ask(\d+)\.lean$", lean_path)
    if not m:
        print(f"Cannot infer task_id from filename: {lean_path}")
        sys.exit(1)
    return int(m.group(1))

def extract_python_code(jsonl_path: str, task_id: int) -> str:
    with open(jsonl_path, "r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("task_id") == task_id:
                return obj.get("code", "")
    print(f"ERROR: No entry with task_id={task_id} found in {jsonl_path}")
    sys.exit(1)

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

def detect_style_from_path(lean_path: str) -> str:
    """Detect the code style from the file path (Imperative/, Functional/, Free_code/)."""
    path_parts = Path(lean_path).parts
    if "Imperative" in path_parts:
        return "Imperative"
    elif "Functional" in path_parts:
        return "Functional"
    elif "Free_code" in path_parts:
        return "Free_code"
    # Default to Functional if not in a specific subdirectory
    return "Functional"

def load_system_base_for_style(style: str) -> str:
    """Load the appropriate fix_system_base prompt based on style."""
    if style == "Imperative":
        return load_prompt("fix_system_base_imperative.txt")
    elif style == "Functional":
        return load_prompt("fix_system_base_functional.txt")
    elif style == "Free_code":
        return load_prompt("fix_system_base_free_code.txt")
    else:
        # Default fallback
        return load_prompt("fix_system_base.txt")

SYSTEM_RETRY_APPEND = load_prompt("fix_system_retry_append.txt")
STRING_IDIOMS_HINT = load_prompt("fix_string_idioms_hint.txt")
API_HINT = load_prompt("fix_api_hint.txt")

def needs_string_rewrite(diags: List[Dict]) -> bool:
    """Detect deprecation around String.get / String.Pos in diagnostics."""
    bad = ("String.get", "String.get!", "String.Pos", "String.Pos.Raw", "String.extract")
    text = " ".join(d.get("message","") for d in diags)
    return any(b in text for b in bad)

def build_user_prompt(lean_code: str, python_code: Optional[str], diags: List[Dict], treat_warnings_as_errors: bool) -> str:
    summary = {
        "treat_warnings_as_errors": treat_warnings_as_errors,
        "diagnostics": diags,
    }

    prompt = f"# Original Lean file:\n{lean_code}\n\n"

    # Only include Python code if it's provided (not Free_code style)
    if python_code:
        prompt += f"# Original Python code:\n{python_code}\n\n"

    prompt += f"# Lean diagnostics (errors and warnings):\n{json.dumps(summary, indent=2)}\n"

    return prompt

async def call_claude_fix_async(system_prompt: str, user_prompt: str) -> str:
    """Async call to Claude Agent SDK for fixing code."""
    # Combine system and user prompts
    full_prompt = f"{system_prompt}\n\n{user_prompt}"

    # Collect response from streaming API
    response_text = ""
    async for message in query(prompt=full_prompt):
        response_text += str(message)

    if not response_text:
        raise RuntimeError("Claude Agent SDK: empty response")

    return response_text

def call_claude_fix(system_prompt: str, user_prompt: str) -> str:
    """Synchronous wrapper for async Claude call."""
    return anyio.run(call_claude_fix_async, system_prompt, user_prompt)

# ------------------- Output normalizer -------------------

FENCE_RE = re.compile(r"^\s*```(?:lean)?\s*|\s*```\s*$", re.IGNORECASE)

def normalize_lean_source(s: str) -> str:
    """
    - Strip code fences if present.
    - Ensure header lines appear *exactly once* and at top:
         import Batteries
         open Std
    """
    if not s:
        return s
    s = FENCE_RE.sub("", s).strip()
    lines = [ln.rstrip() for ln in s.splitlines()]
    body = [ln for ln in lines if ln.strip() not in ("import Batteries", "open Std")]
    fixed = ["import Batteries", "open Std"]
    if body and body[0].strip() != "":
        fixed.append("")
    fixed.extend(body)
    return "\n".join(fixed).lstrip("\ufeff")

# ------------------- Hard-ban checker -------------------

BANNED_TOKENS = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\bunsafe\b",
    r"\baxiom\b",
    r"\bpartial\b",
    r"\bString\.get!?(\b|_)",     # String.get or String.get!
    r"\bString\.extract\b",
    r"\bString\.Pos(\b|\.Raw\b)",
    r"\bStd\.HashMap\.findD\b",
]

def violates_hard_bans(code: str) -> list[str]:
    offenders = []
    for pat in BANNED_TOKENS:
        if re.search(pat, code):
            offenders.append(pat)
    return offenders

# ------------------- Main -------------------

def main():
    # CLI: lean_file, dataset_jsonl, plus flags
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("lean_file")
    ap.add_argument("dataset_jsonl")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--allow-warnings", action="store_true",
                   help="Do not fail or repair on warnings (errors still repaired).")
    g.add_argument("--treat-warnings-as-errors", action="store_true",
                   help="Force-fail on warnings (default).")
    ap.add_argument("--max-repair-rounds", type=int, default=4,
                   help="Max GPT repair attempts (default: 4).")
    args = ap.parse_args()

    # Default policy: treat warnings as errors unless --allow-warnings is given
    treat_warn = args.treat_warnings_as_errors or (not args.allow_warnings)

    lean_path = args.lean_file
    dataset_path = args.dataset_jsonl

    if not os.path.exists(lean_path) or not os.path.exists(dataset_path):
        print("Usage: python fix_lean.py [--allow-warnings|--treat-warnings-as-errors] <lean_file> <dataset_jsonl>")
        print("Note: dataset_jsonl should match the style: mblp-temp_functional.jsonl, mblp-temp_imperative.jsonl, or mblp-temp_free_code.jsonl")
        sys.exit(1)

    task_id = extract_task_id(lean_path)
    lean_code = open(lean_path, "r", encoding="utf-8").read()

    # Detect style from path
    style = detect_style_from_path(lean_path)
    print(f"[fix_lean] Detected style: {style}")

    # Only extract Python code if not Free_code style
    python_code = None
    if style != "Free_code":
        python_code = extract_python_code(dataset_path, task_id)

    diags = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
    blocking = [d for d in diags if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

    if not blocking:
        if diags:
            print(f"[fix_lean] Lean compiles. {len(diags)} warning(s) present.")
        else:
            print("[fix_lean] Lean compiles cleanly (no errors, no warnings).")
        return

    print(f"[fix_lean] Found {len(blocking)} blocking diagnostic(s). Sending to Claude Agent SDK...")

    # Load style-specific base prompt + conditional API hints
    SYSTEM_BASE = load_system_base_for_style(style)
    system_prompt = SYSTEM_BASE
    diag_text = " ".join(d.get("message","") for d in diags)
    if "findD" in diag_text or "HashMap.findD" in diag_text or needs_string_rewrite(diags):
        system_prompt += API_HINT
    if needs_string_rewrite(diags):
        system_prompt += STRING_IDIOMS_HINT

    user_prompt = build_user_prompt(lean_code, python_code, diags, treat_warn)

    fixed_code = None
    for attempt in range(args.max_repair_rounds):
        raw = call_claude_fix(system_prompt, user_prompt)
        candidate = normalize_lean_source(raw)

        # If identical, strengthen the instruction and retry
        if candidate.strip() == lean_code.strip():
            print("[fix_lean] Model returned identical code; retrying with stricter prompt…")
            system_prompt = SYSTEM_BASE + API_HINT + STRING_IDIOMS_HINT + SYSTEM_RETRY_APPEND
            continue

        # Reject outputs that still contain banned tokens/APIs
        offenders = violates_hard_bans(candidate)
        if offenders:
            print(f"[fix_lean] Candidate violates hard bans ({len(offenders)} issue(s)); retrying…")
            system_prompt = SYSTEM_BASE + API_HINT + STRING_IDIOMS_HINT + SYSTEM_RETRY_APPEND
            # do not write invalid candidate; retry
            continue

        # Write candidate and re-check
        with open(lean_path, "w", encoding="utf-8") as f:
            f.write(candidate)

        diags2 = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
        blocking2 = [d for d in diags2 if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

        if not blocking2:
            fixed_code = candidate
            if diags2:
                print(f"[fix_lean] Repaired (non-blocking {len(diags2)} warning(s) remain but allowed).")
            else:
                print("[fix_lean] Repaired (no errors, no warnings)")
            break

        # Prepare next round with stricter instructions
        lean_code = candidate
        user_prompt = build_user_prompt(lean_code, python_code, diags2, treat_warn)
        system_prompt = SYSTEM_BASE + API_HINT + STRING_IDIOMS_HINT + SYSTEM_RETRY_APPEND
        print(f"[fix_lean] Still {len(blocking2)} blocking diagnostic(s); retrying…")

    if fixed_code is None:
        diags_final = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
        print(f"[fix_lean] Still failing after {args.max_repair_rounds} attempt(s). "
              f"Blocking diagnostic(s): {sum(1 for d in diags_final if (d['kind']=='error') or (treat_warn and d['kind']=='warning'))}")
        for d in diags_final[:6]:
            where = f"line {d['line']}" if d['line'] is not None else "line ?"
            print(f"  - [{d['kind']}] {where}: {d['message']}")

if __name__ == "__main__":
    import argparse
    import shutil
    from pathlib import Path

    main()  # run as usual

    # After successful compilation (with or without warnings), move file to Validated/
    try:
        # parse args manually to get lean file path and dataset
        ap = argparse.ArgumentParser()
        ap.add_argument("lean_file")
        ap.add_argument("dataset_jsonl")
        ap.add_argument("--allow-warnings", action="store_true")
        ap.add_argument("--treat-warnings-as-errors", action="store_true")
        _args, _ = ap.parse_known_args()

        lean_path = Path(_args.lean_file).resolve()
        treat_warn = _args.treat_warnings_as_errors or (not _args.allow_warnings)

        # Run final Lean check
        diags = run_lean_check(str(lean_path), treat_warnings_as_errors=treat_warn)
        blocking = [d for d in diags if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

        if not blocking:
            validated_dir = lean_path.parent / "Validated"
            validated_dir.mkdir(exist_ok=True)
            target = validated_dir / lean_path.name
            shutil.move(str(lean_path), str(target))
            print(f"[fix_lean] File validated and moved to {target}")
        else:
            print(f"[fix_lean] Not moved: {len(blocking)} blocking diagnostic(s) remain.")
    except Exception as e:
        print(f"[fix_lean] WARNING: could not check/move validated file: {e}")
