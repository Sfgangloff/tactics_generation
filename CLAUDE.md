# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository contains experiments on automated generation of tactics for theorem proving in Lean 4. The project translates Python programming tasks into Lean 4 implementations using LLM-based code generation, with automatic validation and iterative fixing.

## High-Level Architecture

### Translation Pipeline (Python → Lean)

The codebase implements a multi-stage pipeline:

1. **Input**: Python problems from `data/mbpp.jsonl` (MBPP benchmark dataset)
2. **Translation**: `convert_to_lean.py` uses OpenAI's API to translate Python code to Lean 4
3. **Validation**: `fix_lean.py` runs Lean compiler checks and iteratively fixes errors using LLM feedback
4. **Organization**: Successfully compiled files are moved to `TacticsGeneration/Tasks/Validated/`

### Key Design Constraints

The translation process enforces strict constraints to ensure Lean 4 compatibility:

- **Only Batteries/Std libraries** - no Mathlib, no external dependencies beyond `batteries`
- **Forbidden patterns**: No `sorry`, `admit`, `axiom`, `partial`, deprecated string APIs (`String.get`, `String.Pos`), or library sorts
- **Set operations**: Must use `Std.HashSet`, never `Finset` (which requires Mathlib)
- **String operations**: Only `String.length`, `String.take`, `String.drop`, or convert to `List Char` via `.data`

### Directory Structure

- `TacticsGeneration/` - Lean 4 library
  - `Benchmark.lean` - Manual benchmark with 10 curated tasks (ground truth)
  - `Test*.lean` - Experiment results with LLM feedback notes
  - `Tasks/` - Auto-generated Lean translations (unvalidated)
  - `Tasks/Validated/` - Successfully compiled translations
- Python scripts at root level (translation tooling)
- `data/` - JSONL datasets
  - `mbpp.jsonl` - Source Python benchmark
  - `mblp.jsonl` - Output: translation results with metadata

## Common Commands

### Running Tests/Validation

```bash
# Build the entire Lean project
lake build

# Type-check a specific Lean file with Lake
lake env lean TacticsGeneration/Tasks/Task123.lean

# Run fix_lean to validate and auto-repair a translation
python fix_lean.py TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Allow warnings (only fix errors)
python fix_lean.py --allow-warnings TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Treat warnings as errors (default)
python fix_lean.py --treat-warnings-as-errors TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl
```

### Translation Workflow

```bash
# Translate N new Python tasks to Lean (skips existing task_ids in output)
python convert_to_lean.py \
  --input data/mbpp.jsonl \
  --output data/mblp.jsonl \
  --n 10 \
  --model gpt-5 \
  --lean-out TacticsGeneration/Tasks

# The script automatically:
# - Calls OpenAI API to translate Python → Lean
# - Writes .lean files to TacticsGeneration/Tasks/
# - Runs fix_lean.py automatically on each generated file
# - Moves validated files to TacticsGeneration/Tasks/Validated/
```

### Cleanup Operations

```bash
# Remove all comments and namespace declarations from Lean files
python clean_lean_files.py TacticsGeneration/Tasks/

# This strips:
# - Block/line comments
# - Namespace declarations
# - Duplicate 'open' lines
# - Task prefixes in #guard lines
```

## Python Environment Setup

```bash
# Create virtual environment
python -m venv .venv
source .venv/bin/activate  # or `.venv\Scripts\activate` on Windows

# Install dependencies
pip install -r requirements.txt

# Configure OpenAI API key
echo "your-api-key-here" > openai_key.txt
# Or export OPENAI_API_KEY environment variable
```

## Lean Project Setup

This is a Lake-based Lean 4 project (configured via `lakefile.toml`):

```bash
# Install Lake dependencies (Batteries)
lake update

# Build all targets
lake build

# Run the main executable
lake exe tactics_generation
```

## Key Implementation Details

### Two-Phase LLM Translation

1. **Initial translation** (`convert_to_lean.py`):
   - Uses few-shot examples from `few_shots.txt`
   - Generates JSON with `lean_code`, `lean_tests`, and `notes`
   - Helper `write_lean_from_entry.py` writes structured .lean files

2. **Iterative repair** (`fix_lean.py`):
   - Runs `lake env lean` to type-check
   - On errors/warnings: sends diagnostics + Python reference back to LLM
   - Up to 4 repair rounds with increasingly strict prompts
   - Validates hard-ban violations (no `sorry`, deprecated APIs)
   - Successful files auto-moved to `Validated/` subdirectory

### Benchmark Structure

`TacticsGeneration/Benchmark.lean` contains 10 manually coded tasks representing expected quality:
- Dynamic programming (min cost path, domino tilings)
- Set operations (shared elements using HashSet)
- Number theory (primality checking)
- Heap algorithms (k-largest/smallest elements)
- String manipulation (rotation detection, word filtering)
- List operations (mapping, filtering)

Each task includes:
- Problem description as comment
- Implementation code
- `#guard` test assertions

Test files (`Test*.lean`) document experiment iterations with feedback annotations.

## Important Conventions

### Lean Code Generation Rules

When modifying generated Lean code:
- First two lines must always be `import Batteries` and `open Std`
- Use imperative style (`Id.run do`, mutable arrays, for loops) for algorithm implementations
- Prefer `Array` over `List` for indexed operations
- Use `HashSet.ofList` and `HashSet.filter` for set operations
- Never use sorting functions for set operations (compare as HashSets instead)
- For string indexing: convert to `List Char` via `.data`, manipulate, then `String.mk`

### Task ID System

- Task IDs come from `task_id` field in `mbpp.jsonl`
- Generated files named `Task{id}.lean` (e.g., `Task123.lean`)
- Module name matches filename: `Task123`
- `convert_to_lean.py` tracks processed task_ids to avoid reprocessing

## Troubleshooting

### Common Lean Compilation Issues

1. **"unknown module prefix 'Batteries'"**
   - Ensure running from Lake project root
   - Use `lake env lean` instead of plain `lean`

2. **Deprecated string API errors**
   - Never use `String.get`, `String.get!`, `String.extract`, `String.Pos`
   - Use `s.take k`, `s.drop k`, or `s.data` with `String.mk`

3. **HashMap lookup errors**
   - Use `(m.find? k).getD defaultValue` pattern
   - `Std.HashMap.findD` does not exist in Batteries

4. **Import/module errors**
   - Check `lake-manifest.json` is up to date
   - Run `lake update` to fetch dependencies
   - Ensure project built with `lake build`

### LLM Translation Issues

If translations consistently fail:
- Check `openai_key.txt` is present and valid
- Verify few-shot examples in `few_shots.txt` follow current constraints
- Review `--max-repair-rounds` parameter in `fix_lean.py` (default: 4)
- Check model availability (`--model gpt-5` in `convert_to_lean.py`)

## File Generation Details

- `write_lean_from_entry.py`: Utility that merges imports, adds auto-generated headers, and structures code/tests
- Generated files include auto-comment: `/-! Auto-generated from task {id}. Module: Task{id} -/`
- Import deduplication preserves first occurrence order
- Tests separated by `-- Tests` comment