# Automated Lean 4 Code Generation and Repair

This repository contains an LLM-based system for generating and repairing Lean 4 code. The current implementation focuses on translating programming tasks into Lean 4 implementations with automatic validation and iterative error correction. The project serves as foundational infrastructure for future work in automated theorem proving.

## What This System Does

1. **Generate Lean 4 code** from structured task descriptions using OpenAI's API
2. **Automatically repair** compilation errors and warnings through iterative LLM feedback
3. **Validate** generated code against strict constraints (no `sorry`, deprecated APIs, etc.)
4. **Organize** successfully compiled files into a validated directory

## Quick Start

### Prerequisites

- Lean 4 with Lake ([installation guide](https://leanprover.github.io/lean4/doc/setup.html))
- Python 3.8+
- OpenAI API key ([get one here](https://platform.openai.com/api-keys))

### Installation

```bash
# Install Python dependencies
python3 -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate
pip install -r requirements.txt

# Configure OpenAI API key
echo "your-api-key-here" > openai_key.txt

# Set up Lean project
lake update
lake build
```

## Usage

### Generating Lean Code from Tasks

Translate tasks from JSONL format into Lean 4 code:

```bash
python3 scripts/convert_to_lean.py \
  --input data/mbpp.jsonl \
  --output data/mblp.jsonl \
  --n 10 \
  --model gpt-5 \
  --lean-out TacticsGeneration/Tasks
```

**What it does:**
1. Reads task descriptions from input JSONL (task_id, text, code, tests)
2. Uses few-shot prompting (from `prompts/few_shots.txt`) to generate Lean code
3. Writes `.lean` files to `TacticsGeneration/Tasks/`
4. Automatically runs `fix_lean.py` on each generated file
5. Records results in output JSONL

**Input format** (`data/mbpp.jsonl`):
```json
{
  "task_id": 1,
  "text": "Write a function to check if a number is prime",
  "code": "def is_prime(n): ...",
  "test_list": ["assert is_prime(2) == True", "assert is_prime(4) == False"]
}
```

### Repairing Lean Files

Fix compilation errors in existing Lean files:

```bash
# Basic repair
python3 scripts/fix_lean.py TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Allow warnings (stricter: treat warnings as errors is default)
python3 scripts/fix_lean.py --allow-warnings TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Adjust repair attempts (default: 4)
python3 scripts/fix_lean.py --max-repair-rounds 6 TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl
```

**How it works:**
1. Compiles the file with `lake env lean` and captures diagnostics
2. Sends errors/warnings + original code to LLM for repair
3. Validates the fix (checks for banned tokens like `sorry`, `admit`)
4. Repeats with progressively stricter prompts if issues remain
5. Moves successfully validated files to `TacticsGeneration/Tasks/Validated/`

### Utility Scripts

```bash
# Remove comments, namespaces, and duplicates from Lean files
python3 scripts/clean_lean_files.py TacticsGeneration/Tasks/

# Extract Lean code and tests from validated files into JSONL
python3 scripts/re_json.py data/mbpp.jsonl TacticsGeneration/Tasks/Validated/ data/output.jsonl
```

## Project Structure

```
tactics_generation/
├── scripts/                      # Python tooling (run from project root)
│   ├── convert_to_lean.py       # Generate Lean code from JSONL tasks
│   ├── fix_lean.py              # Iterative repair system
│   ├── write_lean_from_entry.py # Structures Lean files (imports, tests)
│   ├── clean_lean_files.py      # Code cleanup utility
│   └── re_json.py               # Extract code/tests to JSONL
├── prompts/                      # LLM prompt templates (customizable)
│   ├── convert_system_instructions.txt
│   ├── convert_user_template.txt
│   ├── few_shots.txt            # Few-shot examples for generation
│   ├── fix_system_base.txt
│   └── ...
├── TacticsGeneration/            # Lean 4 library
│   ├── Benchmark.lean           # 10 manually coded reference tasks
│   ├── Test*.lean               # Experiment results with annotations
│   ├── Tasks/                   # Auto-generated Lean files
│   └── Tasks/Validated/         # Successfully compiled files
├── data/
│   ├── mbpp.jsonl               # Input: Python programming tasks
│   └── mblp.jsonl               # Output: translation results
├── openai_key.txt               # Your API key (gitignored)
├── lakefile.toml                # Lean project configuration
└── README.md                    # This file
```

## Current Benchmarks

### Manual Benchmark (`TacticsGeneration/Benchmark.lean`)

10 manually coded tasks representing target quality:
- **Dynamic programming**: min cost path, domino tilings
- **Set operations**: shared elements using HashSet
- **Number theory**: primality checking
- **Heap algorithms**: k-largest/smallest elements
- **String manipulation**: rotation detection, word filtering
- **List operations**: mapping, filtering

Each includes problem description, implementation, and `#guard` test assertions.

### Experiment Results (`TacticsGeneration/Test*.lean`)

Files documenting LLM generation experiments with feedback annotations.

## Code Generation Constraints

The system enforces strict rules for generated Lean code:

- **Header**: Must start with `import Batteries` and `open Std`
- **Libraries**: Only Batteries/Std (no Mathlib currently)
- **Forbidden**: `sorry`, `admit`, `axiom`, `partial`, deprecated APIs
- **String operations**: Use `String.take`, `String.drop`, or `.data` (List Char)
- **Set operations**: Use `Std.HashSet` (not `Finset`)

These constraints ensure all generated code compiles without placeholders.

## Customizing Prompts

All prompts are externalized in `prompts/` for easy modification:

- **Generation prompts**: `convert_system_instructions.txt`, `convert_user_template.txt`
- **Repair prompts**: `fix_system_base.txt`, `fix_system_retry_append.txt`
- **Guidance**: `fix_api_hint.txt`, `fix_string_idioms_hint.txt`
- **Examples**: `few_shots.txt`

Edit these files to adjust system behavior without changing code.

## Examples

### Example: Generated Fibonacci Function

From this input:
```json
{
  "task_id": 42,
  "text": "Write a function that returns the nth Fibonacci number",
  "code": "def fib(n): return fib(n-1) + fib(n-2) if n > 1 else n",
  "test_list": ["assert fib(0) == 0", "assert fib(5) == 5"]
}
```

The system generates:
```lean
import Batteries
open Std

/-!
  Auto-generated from task 42.
  Module: Task42
-/

def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- Tests
#guard fib 0 == 0
#guard fib 5 == 5
```

## Troubleshooting

### Common Issues

**"unknown module prefix 'Batteries'"**
- Run `lake update` and `lake build` from project root
- Use `lake env lean` instead of plain `lean` for type-checking

**Scripts fail with import errors**
- Always run scripts from project root: `python3 scripts/fix_lean.py ...`
- Use `python3` not `python`

**OpenAI API errors**
- Check `openai_key.txt` exists at project root and is valid
- Increase timeout: `python3 scripts/convert_to_lean.py --timeout 180 ...`

**Repair system not fixing errors**
- Increase rounds: `--max-repair-rounds 6`
- Check compilation manually: `lake env lean TacticsGeneration/Tasks/Task123.lean`
- Review/edit prompts in `prompts/fix_system_base.txt`

## Technical Details

See [CLAUDE.md](CLAUDE.md) for comprehensive technical documentation including:
- Detailed architecture
- Development roadmap (multi-agent theorem proving)
- Implementation details
- Contributing guidelines

## Resources

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [OpenAI API Docs](https://platform.openai.com/docs/api-reference)

---

**Note**: This is an actively evolving project. Current implementation focuses on code generation; future work will extend to mathematical theorem proving and multi-agent systems.