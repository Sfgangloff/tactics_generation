from pathlib import Path
from typing import Tuple, List, Dict, Any

def _split_imports(lean_text: str) -> Tuple[List[str], str]:
    """
    Split a Lean snippet into (imports, body).
    Keeps import lines exactly as written (leading/trailing spaces stripped),
    and returns the remaining body without those import lines.
    """
    if not lean_text:
        return [], ""
    imports = []
    body_lines = []
    for line in lean_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped)
        else:
            body_lines.append(line)
    # Normalize imports (dedupe while preserving order)
    seen = set()
    dedup_imports = []
    for s in imports:
        if s not in seen:
            seen.add(s)
            dedup_imports.append(s)
    return dedup_imports, "\n".join(body_lines).strip("\n")

def _merge_unique_in_order(a: List[str], b: List[str]) -> List[str]:
    """
    Merge two ordered lists with de-duplication, preserving the first occurrence order.
    """
    out = []
    seen = set()
    for x in a + b:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out

def write_lean_from_entry(entry: Dict[str, Any], out_dir: str) -> Path:
    """
    Given one conversion result entry (like the one you pasted),
    write a single Lean file:
      <lean_module_name or Task{task_id}>.lean

    The file will contain:
      - merged imports from code and tests (deduped),
      - code body,
      - test body (after a separator comment).
    Returns the path of the file written.
    """
    # Defensive extraction
    task_id = entry.get("task_id")
    lean_result = entry.get("lean_result", {})
    module_name = lean_result.get("lean_module_name") or (f"Task{task_id}" if task_id is not None else "Task")
    lean_code = lean_result.get("lean_code", "") or ""
    lean_tests = lean_result.get("lean_tests", "") or ""

    # Split imports/bodies
    code_imports, code_body = _split_imports(lean_code)
    test_imports, test_body = _split_imports(lean_tests)

    # Merge imports (code-first, then tests)
    all_imports = _merge_unique_in_order(code_imports, test_imports)

    # Build final file content
    parts = []
    if all_imports:
        parts.append("\n".join(all_imports))
        parts.append("")  # blank line

    # Optionally add a file header
    parts.append(f"/-!\n  Auto-generated from task {task_id if task_id is not None else '?'}.\n  Module: {module_name}\n-/" )

    if code_body.strip():
        parts.append(code_body.strip())
    if test_body.strip():
        parts.append("\n-- Tests\n" + test_body.strip())

    final_text = "\n\n".join(p for p in parts if p is not None)

    # Ensure output directory exists and write
    out_path = Path(out_dir)
    out_path.mkdir(parents=True, exist_ok=True)
    file_path = out_path / f"{module_name}.lean"
    file_path.write_text(final_text + "\n", encoding="utf-8")
    return file_path

# ----------------
# Example usage:
# ----------------
if __name__ == "__main__":
    # Put your dict in `entry` (as shown in your message), then:
    import json
    raw = r'''{"task_id": 3, "status": "ok", "input_item": {"text": "Write a python function to identify non-prime numbers.", "code": "import math\r\ndef is_not_prime(n):\r\n    result = False\r\n    for i in range(2,int(math.sqrt(n)) + 1):\r\n        if n % i == 0:\r\n            result = True\r\n    return result", "task_id": 3, "test_setup_code": "", "test_list": ["assert is_not_prime(2) == False", "assert is_not_prime(10) == True", "assert is_not_prime(35) == True"], "challenge_test_list": []}, "lean_result": {"task_id": 3, "lean_module_name": "Task3", "lean_code": "import Mathlib.Data.Nat.Basic\n\n-- Precondition: n ≥ 2\n\ndef isNotPrime (n : Nat) : Bool := Id.run do\n  for i in [2 : Nat.sqrt n + 1] do\n    if n % i == 0 then\n      return true\n  return false\n", "lean_tests": "#guard isNotPrime 2 == false\n#guard isNotPrime 10 == true\n#guard isNotPrime 35 == true\n", "notes": ["Assumed Nat for positive numbers. Precondition: n ≥ 2.", "Used Nat.sqrt for finding integer square root."]}}'''
    entry = json.loads(raw)
    path = write_lean_from_entry(entry, out_dir="TacticsGeneration/Tasks")
    print(f"Wrote: {path}")