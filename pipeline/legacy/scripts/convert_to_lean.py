#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
convert_to_lean.py

Read up to N *new* items (i.e., task_ids not already present in the output JSONL)
from a JSONL dataset whose entries look like:
{
  "text": "...",
  "code": "...",
  "task_id": 1,
  "test_setup_code": "",
  "test_list": ["assert ...", ...],
  "challenge_test_list": []
}

For each new item, call Claude Agent SDK to translate the Python code + tests
into Lean 4 (constrained to Batteries/Std), write a .lean file, and
append a line to an output JSONL file.

Usage:
  1) Configure Claude Agent SDK authentication (see SDK documentation)
  2) Few-shots live in few_shots.txt
  3) Run:
     python scripts/convert_to_lean.py \
        --input data/mbpp.jsonl \
        --output data/mblp.jsonl \
        --n 3 \
        --model claude-sonnet-4 \
        --timeout 6000 \
        --lean-out TacticsGeneration/Tasks \
        --style Imperative

     Note: Output filename will automatically be modified based on style:
     - Functional → data/mblp-temp_functional.jsonl
     - Imperative → data/mblp-temp_imperative.jsonl
     - Free_code → data/mblp-temp_free_code.jsonl
"""

from __future__ import annotations
import argparse
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from typing import Any, Dict, Optional, Set

# --- Claude Agent SDK ---
try:
    from claude_agent_sdk import query
    import anyio
except Exception:
    print("ERROR: Could not import claude_agent_sdk. Install with: pip install claude-agent-sdk", file=sys.stderr)
    raise

# --- Lean writer helper ---
try:
    from write_lean_from_entry import write_lean_from_entry
except Exception as e:
    print("ERROR: Could not import write_lean_from_entry. Make sure write_lean_from_entry.py is present.", file=sys.stderr)
    raise

# ---------------- Few-shot examples ----------------
# Get the project root directory (parent of scripts/)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(SCRIPT_DIR)

def load_optional_file(filename: str) -> str:
    """Load a file from prompts/ directory, return empty string if not found."""
    try:
        with open(os.path.join(PROJECT_ROOT, "prompts", filename), "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        return ""

# ---------------- Prompt templates -----------------

def load_prompt(filename: str) -> str:
    """Load a prompt template from the prompts/ directory."""
    try:
        with open(os.path.join(PROJECT_ROOT, "prompts", filename), "r", encoding="utf-8") as f:
            return f.read()
    except FileNotFoundError:
        print(f"ERROR: Could not find prompt file: prompts/{filename}", file=sys.stderr)
        sys.exit(1)

def load_prompts_for_style(style: str):
    """Load system instructions and user template based on style."""
    if style == "Imperative":
        system = load_prompt("convert_system_instructions_imperative.txt")
        user = load_prompt("convert_user_template_imperative.txt")
    elif style == "Free_code":
        # For now, use the no_python versions for Free_code style
        system = load_prompt("convert_system_instructions_no_python.txt")
        user = load_prompt("convert_user_template_no_python.txt")
    else:  # Functional or default
        system = load_prompt("convert_system_instructions.txt")
        user = load_prompt("convert_user_template.txt")
    return system, user

# ---------------- Utilities -----------------

FENCE_RE = re.compile(r"^\s*```(?:json)?\s*|\s*```\s*$", re.IGNORECASE)

def extract_json(text: str) -> Optional[Dict[str, Any]]:
    if not text:
        return None
    cleaned = FENCE_RE.sub("", text)
    start = cleaned.find("{")
    end = cleaned.rfind("}")
    if 0 <= start < end:
        blob = cleaned[start:end+1]
        for loader in (json.loads, lambda s: json.loads(json.loads(s))):
            try:
                return loader(blob)
            except Exception:
                pass
    cleaned = cleaned.replace("```", "").strip()
    for loader in (json.loads, lambda s: json.loads(json.loads(s))):
        try:
            return loader(cleaned)
        except Exception:
            pass
    return None

def load_jsonl(path: str):
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def append_jsonl(path: str, obj: Dict[str, Any]):
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(obj, ensure_ascii=False) + "\n")

def backoff_sleep(attempt: int, base_delay: float):
    import random
    delay = base_delay * (2 ** attempt) * (1 + 0.1 * random.random())
    time.sleep(delay)

def existing_task_ids(path: str) -> Set[int]:
    """
    Read existing output JSONL (if present) and collect all task_id values.
    Robust to mixed objects as long as they contain an integer 'task_id'.
    """
    ids: Set[int] = set()
    if not os.path.exists(path):
        return ids
    try:
        for rec in load_jsonl(path):
            tid = rec.get("task_id", None)
            if isinstance(tid, int):
                ids.add(tid)
    except Exception as e:
        print(f"[convert_to_lean] WARNING: failed to read existing output '{path}': {e}", flush=True)
    return ids

def generate_style_specific_output(base_output: str, style: str) -> str:
    """
    Generate output filename based on style.
    Example: data/mblp.jsonl + Imperative → data/mblp-temp_imperative.jsonl

    Removes any existing style suffix first to handle cases where user
    specifies data/mblp-temp_functional.jsonl but wants Imperative style.
    """
    from pathlib import Path

    path = Path(base_output)
    stem = path.stem  # e.g., "mblp-temp" or "mblp-temp_functional"

    # Remove existing style suffixes if present
    for suffix in ["_functional", "_imperative", "_free_code"]:
        if stem.endswith(suffix):
            stem = stem[:-len(suffix)]
            break

    # Ensure "-temp" is in the stem (add it if not present)
    if not stem.endswith("-temp"):
        stem = stem + "-temp"

    # Add new style suffix
    style_suffix_map = {
        "Functional": "_functional",
        "Imperative": "_imperative",
        "Free_code": "_free_code",
    }

    style_suffix = style_suffix_map.get(style, "_functional")
    new_stem = stem + style_suffix
    new_path = path.parent / (new_stem + path.suffix)

    return str(new_path)

# ---------------- Claude Agent SDK call -----------------

async def call_claude_async(
    system: str,
    user_prompt: str,
    max_retries: int,
    base_delay: float,
    request_timeout: float,
) -> Dict[str, Any]:
    """Async call to Claude Agent SDK with retry logic."""
    last_err: Optional[BaseException] = None
    for attempt in range(max_retries):
        try:
            print("[convert_to_lean] Calling Claude Agent SDK", flush=True)

            # Combine system and user prompts
            full_prompt = f"{system}\n\n{user_prompt}"

            # Collect response from streaming API
            response_text = ""
            async with anyio.fail_after(request_timeout):
                async for message in query(prompt=full_prompt):
                    response_text += str(message)

            print("[convert_to_lean] Response received", flush=True)

            # Try to extract JSON from response
            obj = extract_json(response_text)
            if obj is not None:
                return obj

            # If no JSON found, return raw response
            return {"raw_response": response_text}

        except TimeoutError:
            print(f"[convert_to_lean] attempt {attempt+1} timed out after {request_timeout}s", flush=True)
            last_err = TimeoutError(f"Claude call exceeded {request_timeout}s")
            if attempt < max_retries - 1:
                backoff_sleep(attempt, base_delay=base_delay)
            else:
                raise last_err
        except Exception as e:
            print(f"[convert_to_lean] attempt {attempt+1} failed: {e}", flush=True)
            last_err = e
            if attempt < max_retries - 1:
                backoff_sleep(attempt, base_delay=base_delay)
            else:
                raise
    if last_err:
        raise last_err
    raise RuntimeError("Unknown failure in call_claude")

def call_claude(
    system: str,
    user_prompt: str,
    max_retries: int,
    base_delay: float,
    request_timeout: float,
) -> Dict[str, Any]:
    """Synchronous wrapper for async Claude call."""
    return anyio.run(call_claude_async, system, user_prompt, max_retries, base_delay, request_timeout)

# ---------------- CLI -----------------

@dataclass
class Args:
    input: str
    output: str
    n: Optional[int]
    model: str
    temperature: float
    max_retries: int
    retry_base_delay: float
    timeout: float
    lean_out: str
    style: str

def parse_args() -> Args:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True, help="Path to input JSONL file.")
    p.add_argument("--output", required=True, help="Path to output JSONL file (appended; existing tasks are skipped).")
    p.add_argument("--n", type=int, default=None, help="Process at most N *new* items (skip those already in --output).")
    p.add_argument("--model", default="claude-sonnet-4", help="Claude model (note: model parameter retained for compatibility but Claude Agent SDK may use its default).")
    p.add_argument("--temperature", type=float, default=0.0)  # intentionally unused
    p.add_argument("--max-retries", type=int, default=5)
    p.add_argument("--retry-base-delay", type=float, default=2.0)
    p.add_argument("--timeout", type=float, default=120.0, help="Per-request timeout in seconds.")
    p.add_argument("--lean-out", default="TacticsGeneration/Tasks", help="Directory to write generated .lean files.")
    p.add_argument("--style", default="Functional", choices=["Functional", "Imperative", "Free_code"],
                   help="Code generation style: Functional, Imperative, or Free_code.")
    a = p.parse_args()
    return Args(
        input=a.input,
        output=a.output,
        n=a.n,
        model=a.model,
        temperature=a.temperature,
        max_retries=a.max_retries,
        retry_base_delay=a.retry_base_delay,
        timeout=a.timeout,
        lean_out=a.lean_out,
        style=a.style,
    )

# ---------------- Main -----------------

def main():
    args = parse_args()

    # Generate style-specific output filename
    style_specific_output = generate_style_specific_output(args.output, args.style)
    print(f"[convert_to_lean] Using output file: {style_specific_output}", flush=True)

    # Load prompts based on style
    SYSTEM_INSTRUCTIONS, USER_TEMPLATE = load_prompts_for_style(args.style)

    # DO NOT clear output file. Instead, read existing task_ids and skip them.
    already_done = existing_task_ids(style_specific_output)
    if already_done:
        print(f"[convert_to_lean] Found {len(already_done)} existing task(s) in {style_specific_output}; will skip them.", flush=True)
    else:
        # Ensure the file exists, so later appends won't fail on a missing directory.
        # (Don't create directories automatically; assume user passed a valid path.)
        if not os.path.exists(style_specific_output):
            # Touch the file (parent must exist).
            open(style_specific_output, "a", encoding="utf-8").close()

    # Note: Claude Agent SDK handles authentication automatically via environment variables
    # No explicit client initialization needed

    processed_new = 0   # number of NEW items we translated this run
    skipped = 0         # number of items skipped because already in output
    seen_input = 0      # total input lines examined

    for item in load_jsonl(args.input):
        if args.n is not None and processed_new >= args.n:
            break
        seen_input += 1

        task_id = item.get("task_id")
        if isinstance(task_id, int) and task_id in already_done:
            skipped += 1
            continue

        text = item.get("text", "")
        code = item.get("code", "")
        test_setup = item.get("test_setup_code", "")
        tests = item.get("test_list", [])
        challenge = item.get("challenge_test_list", [])

        # Prepare format arguments based on style
        if args.style == "Free_code":
            # Free_code template uses different placeholder names
            format_args = {
                "task_id": task_id,
                "text": text,
                "requirements": test_setup if test_setup else "(none)",
                "test_cases": "\n".join(f"- {t}" for t in tests) if tests else "(none)",
                "challenge_requirements": "\n".join(f"- {t}" for t in challenge) if challenge else "(none)",
                "fewshots": load_optional_file("few_shots_no_python.txt"),
            }
        else:
            # Functional and Imperative styles use original placeholders
            format_args = {
                "task_id": task_id,
                "text": text,
                "code": code,
                "test_setup_code": test_setup,
                "tests": "\n".join(f"- {t}" for t in tests),
                "challenge_tests": "\n".join(f"- {t}" for t in challenge) if challenge else "(none)",
            }

            # Add style-specific examples
            if args.style == "Functional":
                format_args["fewshots"] = load_optional_file("few_shots_no_python.txt")
            elif args.style == "Imperative":
                format_args["imperative_example"] = load_optional_file("example_imperative_programming")
                format_args["fewshots"] = load_optional_file("few_shots_imperative.txt")  # if it exists

        user_prompt = USER_TEMPLATE.format(**format_args)

        print(f"[convert_to_lean] Task {task_id} initiated", flush=True)

        try:
            result = call_claude(
                system=SYSTEM_INSTRUCTIONS,
                user_prompt=user_prompt,
                max_retries=args.max_retries,
                base_delay=args.retry_base_delay,
                request_timeout=args.timeout,
            )
        except Exception as e:
            out = {
                "task_id": task_id,
                "status": "error",
                "error": repr(e),
                "input_item": item,
            }
            append_jsonl(style_specific_output, out)
            processed_new += 1  # Count this as handled (we won't retry it in future runs).
            continue

        # Try to write the .lean file
        lean_file_path = None
        try:
            entry_for_writer = {
                "task_id": task_id,
                "lean_result": result,  # expects lean_module_name / lean_code / lean_tests
            }
            if isinstance(result, dict) and all(k in result for k in ("lean_code", "lean_tests")):
                lean_file_path = write_lean_from_entry(entry_for_writer, out_dir=os.path.join(args.lean_out, args.style))
        except Exception as werr:
            print(f"[convert_to_lean] WARNING: failed to write .lean for task {task_id}: {werr}", flush=True)

        out = {
            "task_id": task_id,
            "status": "ok",
            "input_item": item,
            "lean_result": result,
        }
        if lean_file_path:
            out["lean_file"] = str(lean_file_path)
            # --- Run fix_lean automatically after writing ---
            try:
                print(f"[convert_to_lean] Running fix_lean on {lean_file_path}...", flush=True)
                import subprocess
                fix_lean_path = os.path.join(SCRIPT_DIR, "fix_lean.py")
                subprocess.run(
                    [
                        sys.executable,
                        fix_lean_path,
                        "--allow-warnings",  # or "--treat-warnings-as-errors"
                        str(lean_file_path),
                        args.input,
                    ],
                    check=False,  # keep going even if it fails
                )
            except Exception as fixerr:
                print(f"[convert_to_lean] WARNING: fix_lean failed on {lean_file_path}: {fixerr}", flush=True)

        append_jsonl(style_specific_output, out)
        processed_new += 1

    print(
        f"Examined {seen_input} input item(s). "
        f"Processed {processed_new} new item(s). "
        f"Skipped {skipped} already-done item(s). Output -> {style_specific_output}"
    )

if __name__ == "__main__":
    main()
