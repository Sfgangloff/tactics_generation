#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fix_lean.py

Run Lean (via Lake if present). If there are *any* diagnostics (errors or, by
default, warnings), look up the Python reference code by task_id from a JSONL
dataset, ask gpt-5 to repair the Lean file (eliminating errors AND warnings),
then rewrite the file in place.

Usage:
    python fix_lean.py TacticsGeneration/Tasks/Task11.lean data/mbpp.jsonl
    # optional:
    python fix_lean.py --allow-warnings TacticsGeneration/Tasks/Task11.lean data/mbpp.jsonl
"""

import subprocess
import json
import os
import re
import sys
import shutil
from pathlib import Path
from typing import List, Dict, Optional
from openai import OpenAI

OPENAI_MODEL = "gpt-5"
OPENAI_KEY_PATH = "openai_key.txt"  # or env OPENAI_API_KEY

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

# ------------------- OpenAI -------------------

def load_openai_client() -> OpenAI:
    key = None
    if os.path.exists(OPENAI_KEY_PATH):
        key = open(OPENAI_KEY_PATH, "r", encoding="utf-8").read().strip()
    else:
        key = os.environ.get("OPENAI_API_KEY")
    if not key:
        print("Missing OpenAI key. Provide via openai_key.txt or OPENAI_API_KEY.")
        sys.exit(1)
    return OpenAI(api_key=key)

SYSTEM_BASE = (
    "You are an expert Lean 4 and Python translator.\n"
    "You receive a Lean file generated from Python code.\n"
    "Fix ALL Lean compilation issues while keeping the Lean code as close as possible "
    "to a literal translation of the Python code.\n"
    "Do NOT modify the tests or their logic.\n"
    "Eliminate all warnings as well (unused vars, shadowed names, non-exhaustive matches, deprecations, etc.).\n"
    "\n"
    "PRIOR THINKING (DO NOT OUTPUT):\n"
    "- First read the Lean file carefully and construct for yourself a concise, line-by-line explanation of what each line does\n"
    "  and how it corresponds to the provided Python reference.\n"
    "- Use that internal explanation to plan the minimal, correct repair. Do not include *any* of this explanation in your reply.\n"
    "- Your reply must still follow the STRICT OUTPUT RULES below and contain only the final Lean source code.\n"
    "\n"
    "STRICT OUTPUT RULES:\n"
    "1) Return ONLY raw Lean source code (no markdown fences, no ```lean, no explanations).\n"
    "2) The first two lines MUST be exactly:\n"
    "     import Batteries\n"
    "     open Std\n"
    "3) Do not remove existing tests; keep their module placement.\n"
    "\n"
    "ABSOLUTE BANS:\n"
    "- NEVER use: `sorry`, `admit`, `by admit`, `by sorry`, `unsafe`, `axiom`, `partial`.\n"
    "- NEVER use deprecated or unavailable APIs: `String.get`, `String.get!`, `String.extract`, `String.Pos`, `String.Pos.Raw`, "
    "`Std.HashMap.findD`.\n"
    "\n"
    "STRING RULES:\n"
    "- If indexing/slicing is needed, use only `String.length`, `String.take`, `String.drop`, or convert to `List Char` via `s.data` "
    "  and rebuild with `String.mk`.\n"
    "\n"
    "HASHMAP/HASHSET RULES (Std/Batteries-compatible):\n"
    "- For maps, use: `insert`, `erase`, `contains`, `find? : α → Option β`, and combine with `Option.getD` or a `match` to supply defaults.\n"
    "  Example: `let v := (m.find? k).getD defVal`  -- not `findD`.\n"
    "- For sets, use `Std.HashSet` (`insert`, `erase`, `contains`, `fold`, etc.). Do NOT use `Finset`.\n"
)

SYSTEM_RETRY_APPEND = (
    "\nYour previous output did not resolve the reported diagnostics or was identical to the input.\n"
    "You MUST alter the Lean code to eliminate ALL errors and warnings while preserving tests.\n"
)

def needs_string_rewrite(diags: List[Dict]) -> bool:
    """Detect deprecation around String.get / String.Pos in diagnostics."""
    bad = ("String.get", "String.get!", "String.Pos", "String.Pos.Raw", "String.extract")
    text = " ".join(d.get("message","") for d in diags)
    return any(b in text for b in bad)

STRING_IDIOMS_HINT = (
    "\nIDIOMS YOU MUST USE INSTEAD OF String.get:\n"
    "- Convert to chars: `let cs := s.data : List Char` and traverse/index the list; rebuild with `String.mk cs`.\n"
    "- Or use slices: `s.take k` / `s.drop k` (characters counted in `Nat`).\n"
    "Examples:\n"
    "-- remove char at index i:\n"
    "  let rec dropAt (xs : List Char) (i k : Nat) : List Char :=\n"
    "    match xs with | [] => [] | c::xs =>\n"
    "      let tail := dropAt xs i (k+1)\n"
    "      if k = i then tail else c :: tail\n"
    "  String.mk (dropAt s.data i 0)\n"
    "-- rotate left by k:\n"
    "  (s.drop k) ++ (s.take k)\n"
)

API_HINT = (
    "\nUse these API idioms:\n"
    "- HashMap lookup with default: `let v := (m.find? k).getD defVal` or `match m.find? k with | some v => v | none => defVal`.\n"
    "- Do NOT call `.findD` on HashMap (not available in Std/Batteries).\n"
    "- Avoid `String.get`/`String.get!`/`String.extract`/`String.Pos`; instead use `s.take k`, `s.drop k`, or operate on `s.data` and `String.mk`.\n"
)

def build_user_prompt(lean_code: str, python_code: str, diags: List[Dict], treat_warnings_as_errors: bool) -> str:
    summary = {
        "treat_warnings_as_errors": treat_warnings_as_errors,
        "diagnostics": diags,
    }
    return (
        "# Original Lean file:\n"
        f"{lean_code}\n\n"
        "# Original Python code:\n"
        f"{python_code}\n\n"
        "# Lean diagnostics (errors and warnings):\n"
        f"{json.dumps(summary, indent=2)}\n"
    )

def call_openai_fix(client: OpenAI, system_prompt: str, user_prompt: str) -> str:
    resp = client.responses.create(
        model=OPENAI_MODEL,
        instructions=system_prompt,
        input=[{"role": "user", "content": [{"type": "input_text", "text": user_prompt}]}],
    )
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
        sys.exit(1)

    task_id = extract_task_id(lean_path)
    python_code = extract_python_code(dataset_path, task_id)
    lean_code = open(lean_path, "r", encoding="utf-8").read()

    diags = run_lean_check(lean_path, treat_warnings_as_errors=treat_warn)
    blocking = [d for d in diags if (d["kind"] == "error") or (treat_warn and d["kind"] == "warning")]

    if not blocking:
        if diags:
            print(f"[fix_lean] Lean compiles. {len(diags)} warning(s) present.")
        else:
            print("[fix_lean] Lean compiles cleanly (no errors, no warnings).")
        return

    print(f"[fix_lean] Found {len(blocking)} blocking diagnostic(s). Sending to OpenAI...")
    client = load_openai_client()

    # Base prompt + conditional API hints
    system_prompt = SYSTEM_BASE
    diag_text = " ".join(d.get("message","") for d in diags)
    if "findD" in diag_text or "HashMap.findD" in diag_text or needs_string_rewrite(diags):
        system_prompt += API_HINT
    if needs_string_rewrite(diags):
        system_prompt += STRING_IDIOMS_HINT

    user_prompt = build_user_prompt(lean_code, python_code, diags, treat_warn)

    fixed_code = None
    for attempt in range(args.max_repair_rounds):
        raw = call_openai_fix(client, system_prompt, user_prompt)
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
