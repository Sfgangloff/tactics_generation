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

For each new item, call an OpenAI model to translate the Python code + tests
into Lean 4 (constrained to Batteries/Std), write a .lean file, and
append a line to an output JSONL file.

Usage:
  1) Put your API key in openai_key.txt   (or set OPENAI_API_KEY)
  2) Few-shots live in few_shots.txt
  3) Run:
     python convert_to_lean.py \
        --input data/mbpp.jsonl \
        --output data/mblp.jsonl \
        --n 3 \
        --model gpt-5 \
        --timeout 60 \
        --lean-out TacticsGeneration/Tasks
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
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout

# --- OpenAI SDK (Responses API) ---
try:
    from openai import OpenAI
except Exception:
    print("ERROR: Could not import openai SDK. Install with: pip install openai", file=sys.stderr)
    raise

# --- Lean writer helper ---
try:
    from write_lean_from_entry import write_lean_from_entry
except Exception as e:
    print("ERROR: Could not import write_lean_from_entry. Make sure write_lean_from_entry.py is present.", file=sys.stderr)
    raise

# ---------------- Few-shot examples ----------------
try:
    with open("few_shots.txt", "r", encoding="utf-8") as _fs:
        FEWSHOTS = _fs.read()
except FileNotFoundError:
    FEWSHOTS = ""  # still works; just no in-context examples

# ---------------- Prompt templates -----------------

SYSTEM_INSTRUCTIONS = """\
You are a Lean 4 translator. Convert the given tiny Python function + asserts into **Lean 4** with the LEAST possible deviation.

HARD CONSTRAINTS (must ALL hold):

0) Header imports are FIXED and MANDATORY — at the very top of `lean_code`:
     import Batteries
     open Std
   • Do NOT import anything else. No `Mathlib`, no `open Classical`, no extra packages.
   • Use only what is available in Batteries + Std.

0b) FORBIDDEN identifiers/tokens (if any appear, you MUST regenerate a compliant solution):
   Mathlib, Finset, Multiset, List.toFinset, open Classical, classical, decide, simp, theorem, lemma.
0c) Set-like tasks (e.g., “shared/similar/common elements”):
    • IMPLEMENT WITH Std.HashSet ONLY. Do not use Finset.
    • The function MAY return a HashSet (preferred) if Python used set semantics.
      In that case, ADAPT the tests to compare as sets (unordered), not lists.
    • ABSOLUTELY FORBIDDEN: any sorting or “fake sorting helpers”.
      Do NOT use qsort, List.qsort, List.sort, mergeSort, Array.qsort,
      insertionSort, or any locally-defined sort (e.g., isort/insertBy, etc.).
    • If you need determinism for internal folds, it’s fine; but DO NOT
      transform the public result into a sorted list.

0d) Test adaptation (MANDATORY when 0c applies):
    • If Python built a set (e.g., set(...) & set(...)) and then coerced to tuple,
      treat order as unspecified. In Lean, compare as HashSets:
         #guard decide (similarElements xs ys = Std.HashSet.ofList expected)
    • Do NOT sort to force list equality.
0e) Strings: NEVER use `String.extract`, `String.Pos`, or `String.Pos.Raw`.
    Only use: `String.length`, `String.take`, `String.drop`, `(++)`.
    Example rotation check: `s == (s.drop k) ++ (s.take k)`.

0f) DO NOT use any heap APIs (`BinaryHeap`, `pop?`, etc.).
    Implement deterministically by repeating:
      - find the current minimum with a single `foldl`,
      - remove exactly ONE occurrence of that minimum,
      - append it to the result,
      - repeat up to n times or until the list is empty.
    This must be done with List operations only (no sorting calls, no custom sort).

0g) Sorting ban: Do not call `sort`, `qsort`, `mergeSort`, `isort`, or any sort.
    If Python semantics are set-like but tests assert order, choose a construction
    that produces the required order without sorting. Otherwise compare as sets.
1) No creativity. Do not change the algorithm, control flow, or data structures unless absolutely necessary to make Lean compile or to mirror Python semantics for the given tests.

2) Preserve the public API exactly.
   - Same function name (camelCase OK), same arguments, same return “kind”.
   - Do NOT introduce Option/IO/State/etc. unless Python explicitly models that behavior.
   - If Python assumes valid indices, keep that assumption; put preconditions in a comment.

3) Purity. No printing, no IO. Local mutation via `Id.run` is fine when needed.

4) Tests must mirror Python asserts and deterministically pass.
   - If Python used sets but tests expect order, sort deterministically at the end (e.g. `qsort (· ≤ ·)`) and note it.

5) Imports: only the fixed header from (0). No unused imports.

6) One module per task named `Task{task_id}`; put function and tests in the same file or clearly separated sections.

7) Output format: return ONE JSON object with keys:
   task_id, lean_module_name, lean_code, lean_tests, notes
   No markdown fences. No prose outside JSON.

Type mapping:
- Python int → `Nat` if nonnegative, else `Int` (note in `notes` if ambiguous).
- Python bool → `Bool`.
- Python lists/tuples of ints → `List Nat` / `List Int`.
- **Set-like behavior:** DO NOT use `Finset`. Implement via Batteries/Std only:
  • Either list-based (e.g., `filter` + `any` + a dedup pass like `eraseDups` you define), then `qsort (· ≤ ·)`;
  • Or `Std.HashSet` if helpful — but still no Mathlib/Finset.

Indexing/bounds:
- Follow Python’s implicit assumptions; document preconditions instead of changing return types.

SELF-CHECK before returning:
- `lean_code` must begin exactly with the two header lines and contain none of the forbidden tokens from (0b).
"""

USER_TEMPLATE = """\
Task ID: {task_id}

Translate the following Python LITERALLY to Lean 4, following ALL HARD CONSTRAINTS and STRICT RULES.

Python task description:
{text}

Python code:
{code}

Python test setup (if any):
{test_setup_code}

Python asserts:
{tests}

Challenge tests (if any):
{challenge_tests}

Deliver ONE JSON object:
- task_id: integer
- lean_module_name: "Task{task_id}"
- lean_code: Lean 4 code using ONLY the fixed header (Batteries/Std), no other imports, no IO/prints
- lean_tests: Lean 4 tests that mirror the Python asserts (deterministic; sort if Python used sets but order is asserted)
- notes: brief list of any absolutely necessary deviations (e.g., “sorted after dedup to match asserted order”)

Sorting requirement: do not use any library sort. If you need a deterministic order,
inline the local `isort` helper (see rules) and call `isort (· ≤ ·) …`.

Here are a few examples to help you:

{fewshots}
"""

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

# ---------------- OpenAI call -----------------

def call_openai(
    client: OpenAI,
    model: str,
    system: str,
    user_prompt: str,
    max_retries: int,
    base_delay: float,
    request_timeout: float,
) -> Dict[str, Any]:
    last_err: Optional[BaseException] = None
    for attempt in range(max_retries):
        try:
            print("[convert_to_lean] Calling response", flush=True)
            with ThreadPoolExecutor(max_workers=1) as ex:
                fut = ex.submit(
                    lambda: client.responses.create(
                        model=model,
                        instructions=system,
                        input=[{
                            "role": "user",
                            "content": [{"type": "input_text", "text": user_prompt}],
                        }],
                    )
                )
                try:
                    resp = fut.result(timeout=request_timeout)
                except FuturesTimeout:
                    raise TimeoutError(f"OpenAI call exceeded {request_timeout}s")

            print("[convert_to_lean] Response received", flush=True)

            text = getattr(resp, "output_text", None)
            if isinstance(text, str):
                obj = extract_json(text)
                if obj is not None:
                    return obj

            if hasattr(resp, "output") and isinstance(resp.output, list):
                for item in resp.output:
                    content = getattr(item, "content", None)
                    if isinstance(content, list):
                        for seg in content:
                            seg_text = getattr(seg, "text", None)
                            if isinstance(seg_text, str):
                                obj = extract_json(seg_text)
                                if obj is not None:
                                    return obj
                    itext = getattr(item, "text", None)
                    if isinstance(itext, str):
                        obj = extract_json(itext)
                        if obj is not None:
                            return obj

            return {"raw_response": resp.model_dump() if hasattr(resp, "model_dump") else str(resp)}

        except Exception as e:
            print(f"[convert_to_lean] attempt {attempt+1} failed: {e}", flush=True)
            last_err = e
            if attempt < max_retries - 1:
                backoff_sleep(attempt, base_delay=base_delay)
            else:
                raise
    if last_err:
        raise last_err
    raise RuntimeError("Unknown failure in call_openai")

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

def parse_args() -> Args:
    p = argparse.ArgumentParser()
    p.add_argument("--input", required=True, help="Path to input JSONL file.")
    p.add_argument("--output", required=True, help="Path to output JSONL file (appended; existing tasks are skipped).")
    p.add_argument("--n", type=int, default=None, help="Process at most N *new* items (skip those already in --output).")
    p.add_argument("--model", default="gpt-5", help="OpenAI model (Responses API).")
    p.add_argument("--temperature", type=float, default=0.0)  # intentionally unused with some models
    p.add_argument("--max-retries", type=int, default=5)
    p.add_argument("--retry-base-delay", type=float, default=2.0)
    p.add_argument("--timeout", type=float, default=120.0, help="Per-request timeout in seconds.")
    p.add_argument("--lean-out", default="TacticsGeneration/Tasks", help="Directory to write generated .lean files.")
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
    )

# ---------------- Main -----------------

def main():
    args = parse_args()

    # DO NOT clear output file. Instead, read existing task_ids and skip them.
    already_done = existing_task_ids(args.output)
    if already_done:
        print(f"[convert_to_lean] Found {len(already_done)} existing task(s) in {args.output}; will skip them.", flush=True)
    else:
        # Ensure the file exists, so later appends won't fail on a missing directory.
        # (Don't create directories automatically; assume user passed a valid path.)
        if not os.path.exists(args.output):
            # Touch the file (parent must exist).
            open(args.output, "a", encoding="utf-8").close()

    # --- Load API key ---
    key_path = "openai_key.txt"
    if os.path.exists(key_path):
        api_key = open(key_path, "r", encoding="utf-8").read().strip()
    else:
        api_key = os.environ.get("OPENAI_API_KEY")

    if not api_key:
        print("ERROR: Put your key in 'openai_key.txt' or set OPENAI_API_KEY.", file=sys.stderr)
        sys.exit(1)

    client = OpenAI(api_key=api_key)
    try:
        client = client.with_options(timeout=args.timeout)
    except Exception:
        pass

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

        user_prompt = USER_TEMPLATE.format(
            task_id=task_id,
            text=text,
            code=code,
            test_setup_code=test_setup,
            tests="\n".join(f"- {t}" for t in tests),
            challenge_tests="\n".join(f"- {t}" for t in challenge) if challenge else "(none)",
            fewshots=FEWSHOTS,
        )

        print(f"[convert_to_lean] Task {task_id} initiated", flush=True)

        try:
            result = call_openai(
                client=client,
                model=args.model,
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
            append_jsonl(args.output, out)
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
                lean_file_path = write_lean_from_entry(entry_for_writer, out_dir=args.lean_out)
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
                subprocess.run(
                    [
                        sys.executable,
                        "fix_lean.py",
                        "--allow-warnings",  # or "--treat-warnings-as-errors"
                        str(lean_file_path),
                        args.input,
                    ],
                    check=False,  # keep going even if it fails
                )
            except Exception as fixerr:
                print(f"[convert_to_lean] WARNING: fix_lean failed on {lean_file_path}: {fixerr}", flush=True)

        append_jsonl(args.output, out)
        processed_new += 1

    print(
        f"Examined {seen_input} input item(s). "
        f"Processed {processed_new} new item(s). "
        f"Skipped {skipped} already-done item(s). Output -> {args.output}"
    )

if __name__ == "__main__":
    main()
