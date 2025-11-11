# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This repository is developing a **multi-agent system for automated theorem proving and formalization in Lean 4**. The project aims to:

1. **Formalize theorems** expressed in natural language into Lean 4
2. **Prove new theorems** using automated tactic generation
3. **Correct and repair Lean files** through iterative LLM-based fixing
4. **Discover connections** between mathematical results across different domains
5. **Build a knowledge base** of formalized mathematics

**Current Status**: The project currently includes foundational infrastructure for LLM-based Lean code generation and repair. Initial experiments focused on translating Python programming tasks to Lean 4 as a proof of concept. The system is being progressively evolved toward mathematical theorem proving.

**Note**: This is an actively evolving project. Features and architecture will be refined iteratively as we develop new capabilities.

## High-Level Architecture

### Current Pipeline Components

The existing infrastructure provides:

1. **LLM-based Code Generation** (`scripts/convert_to_lean.py`)
   - Uses OpenAI's API with few-shot prompting to generate Lean 4 code
   - Configurable prompts (stored in `prompts/`)
   - JSON-based structured output

2. **Iterative Repair System** (`scripts/fix_lean.py`)
   - Automatic compilation checking via `lake env lean`
   - Error/warning diagnostics fed back to LLM
   - Multiple repair rounds with increasingly strict prompts
   - Validates against hard-ban violations (no `sorry`, deprecated APIs)
   - Successful files auto-moved to `Validated/` subdirectory

3. **Supporting Utilities**
   - `write_lean_from_entry.py`: Structures Lean files with proper imports/tests
   - `clean_lean_files.py`: Removes comments, namespaces, duplicates
   - `re_json.py`: Extracts Lean code and tests into JSONL format

### Future Multi-Agent Architecture (Planned)

The system will evolve to include:

- **Formalization Agent**: Natural language theorem → Lean formalization
- **Proof Agent**: Automated tactic generation and proof search
- **Repair Agent**: Error correction and iterative fixing (currently implemented)
- **Connection Agent**: Cross-domain mathematical relationship discovery
- **Knowledge Base**: Indexed repository of formalized theorems and proofs

### Lean 4 Coding Constraints

Current code generation enforces these constraints (may evolve for mathematical formalization):

**For non-Mathlib development:**
- **Libraries**: Only Batteries/Std - no external dependencies beyond `batteries`
- **Forbidden patterns**: No `sorry`, `admit`, `axiom`, `partial`, deprecated string APIs
- **Set operations**: Use `Std.HashSet`, not `Finset` (requires Mathlib)
- **String operations**: Only `String.length`, `String.take`, `String.drop`, or `List Char` via `.data`

**For Mathlib development** (future work):
- Full Mathlib imports allowed
- Use existing tactics: `simp`, `ring`, `linarith`, `omega`, etc.
- Leverage Mathlib's algebraic hierarchy
- Follow Mathlib naming conventions and style guide

### Directory Structure

```
tactics_generation/                    # PROJECT ROOT
├── scripts/                          # Python tooling (all executable from here)
│   ├── convert_to_lean.py           # LLM-based Lean code generation
│   ├── fix_lean.py                  # Iterative repair system
│   ├── write_lean_from_entry.py     # Lean file structuring utility
│   ├── clean_lean_files.py          # Code cleanup utility
│   └── re_json.py                   # JSONL extraction utility
├── prompts/                          # LLM prompt templates (externalizable)
│   ├── convert_system_instructions.txt
│   ├── convert_user_template.txt
│   ├── few_shots.txt                # Few-shot examples for code generation
│   ├── fix_system_base.txt
│   ├── fix_system_retry_append.txt
│   ├── fix_string_idioms_hint.txt
│   └── fix_api_hint.txt
├── TacticsGeneration/               # Lean 4 library
│   ├── Benchmark.lean               # Manual benchmark (10 reference tasks)
│   ├── Test*.lean                   # Experiment results with annotations
│   ├── Tasks/                       # Auto-generated Lean files (unvalidated)
│   └── Tasks/Validated/             # Successfully compiled Lean files
├── agents/                           # Multi-agent system components
│   └── search/                      # Search agent for Lean library functions
│       ├── src/                     # Source code
│       │   ├── search_agent.py     # Main CLI and orchestrator
│       │   ├── task_analyzer.py    # LLM keyword extraction
│       │   ├── searcher.py         # Search and ranking
│       │   ├── import_resolver.py  # Import statement generation
│       │   ├── lean_indexer.py     # Index builder
│       │   ├── enrich_index_descriptions.py  # Description generator
│       │   └── database.py         # SQLite operations
│       ├── prompts/                # Agent-specific prompts
│       │   ├── task_analyzer_system.txt
│       │   └── description_enricher_system.txt
│       ├── config/                 # Configuration files
│       │   └── core_namespaces.txt
│       ├── data/                   # Agent data files
│       │   ├── lean_index.json
│       │   ├── enriched_lean_index.json
│       │   └── search_history.db
│       ├── docs/                   # Agent documentation
│       │   └── search_agent_plan.md
│       ├── tests/                  # Agent tests
│       └── README.md               # Agent-specific README
├── data/                            # Project-wide datasets
│   ├── mbpp.jsonl                  # Source data (Python benchmark - legacy)
│   └── mblp.jsonl                  # Translation results with metadata
├── openai_key.txt                  # OpenAI API key (gitignored)
├── lakefile.toml                   # Lean project configuration
└── CLAUDE.md                       # This file
```

**Note:** This structure shows both the legacy code generation tools (scripts/) and the new multi-agent architecture (agents/). When working with files, always verify which subsystem you're working in.

## File Operations Protocol

**CRITICAL: Always verify you are in the correct directory before creating or modifying files.**

### Before Creating/Modifying Files:

1. **Check current working directory** using the environment information provided
2. **Verify the target path** matches the intended location in the project structure
3. **Use absolute paths** when possible to avoid ambiguity
4. **Double-check file locations** against the Directory Structure above

### Example Verification Pattern:

```python
# WRONG: Creating files without checking location
# Could accidentally create in wrong directory!

# RIGHT: Verify location first
# Current working directory: /Users/.../tactics_generation/
# Target file: scripts/new_script.py
# Full path: /Users/.../tactics_generation/scripts/new_script.py
# ✓ Verified - proceed with file creation
```

### Common Mistakes to Avoid:

❌ **Don't assume relative paths** - Always verify against absolute project structure
❌ **Don't create files in parent directories** without explicit confirmation
❌ **Don't modify files** without reading them first to confirm location
✅ **Do check working directory** before any file operation
✅ **Do use absolute paths** for all file operations
✅ **Do verify file exists** at expected location after reading

### Special Considerations:

**For multi-agent projects** (like `agents/search/`):
- Verify you're in the correct agent subdirectory
- Check that paths are relative to the agent root, not project root
- Example: `agents/search/src/search_agent.py` vs `scripts/convert_to_lean.py`

**For Python scripts:**
- All scripts in `scripts/` should be run from project root
- Scripts automatically resolve paths relative to project root
- Verify imports and path resolution match project structure

**For Lean files:**
- Lean files go in `TacticsGeneration/` directory
- Validated files go in `TacticsGeneration/Tasks/Validated/`
- Never create Lean files in `scripts/` or `data/`

## Common Commands

### Lean Project Operations

```bash
# Build the entire Lean project
lake build

# Type-check a specific Lean file with Lake
lake env lean TacticsGeneration/Tasks/Task123.lean

# Run the main executable (if defined in lakefile.toml)
lake exe tactics_generation
```

### Repair and Validation

```bash
# Run fix_lean to validate and auto-repair a Lean file
python3 scripts/fix_lean.py TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Allow warnings (only fix errors)
python3 scripts/fix_lean.py --allow-warnings TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Treat warnings as errors (default - more strict)
python3 scripts/fix_lean.py --treat-warnings-as-errors TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl

# Set maximum repair rounds (default: 4)
python3 scripts/fix_lean.py --max-repair-rounds 6 TacticsGeneration/Tasks/Task123.lean data/mbpp.jsonl
```

### Code Generation (Legacy/Example Workflow)

```bash
# Generate Lean code from JSONL input (example with Python→Lean translation)
python3 scripts/convert_to_lean.py \
  --input data/mbpp.jsonl \
  --output data/mblp.jsonl \
  --n 10 \
  --model gpt-5 \
  --lean-out TacticsGeneration/Tasks

# The script automatically:
# - Calls OpenAI API with prompts from prompts/
# - Writes .lean files to TacticsGeneration/Tasks/
# - Runs fix_lean.py automatically on each generated file
# - Moves validated files to TacticsGeneration/Tasks/Validated/
```

### Utility Operations

```bash
# Clean Lean files (remove comments, namespaces, duplicates)
python3 scripts/clean_lean_files.py TacticsGeneration/Tasks/

# Extract Lean code and tests from validated files into JSONL
python3 scripts/re_json.py data/mbpp.jsonl TacticsGeneration/Tasks/Validated/ data/output.jsonl
```

## Python Environment Setup

```bash
# Create virtual environment
python3 -m venv .venv
source .venv/bin/activate  # or `.venv\Scripts\activate` on Windows

# Install dependencies
pip install -r requirements.txt

# Configure OpenAI API key (stored at project root)
echo "your-api-key-here" > openai_key.txt
# Or export OPENAI_API_KEY environment variable
```

**Note**: All Python scripts are located in `scripts/` and should be run from the project root (e.g., `python3 scripts/fix_lean.py ...`). Scripts automatically resolve paths to `prompts/`, `openai_key.txt`, and data files relative to the project root.

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

### LLM-Based Code Generation System

**Prompt Engineering** (`prompts/` directory):
- System instructions and user templates externalized for easy modification
- Few-shot examples guide code generation style
- Separate prompts for generation vs. repair phases
- Modular prompt components (base, retry, API hints, string idioms)

**Generation Pipeline** (`scripts/convert_to_lean.py`):
1. Load few-shot examples from `prompts/few_shots.txt`
2. Format task-specific user prompt with input data
3. Call OpenAI API (Responses API) with structured JSON output
4. Parse JSON response: `lean_code`, `lean_tests`, `notes`
5. Write structured Lean file via `write_lean_from_entry.py`
6. Automatically trigger repair system

**Iterative Repair System** (`scripts/fix_lean.py`):
1. Run `lake env lean` to type-check and collect diagnostics
2. Extract errors/warnings with line numbers
3. Send diagnostics + original code + reference to LLM
4. Receive corrected code, validate against hard-bans
5. Repeat up to N rounds (default: 4) with stricter prompts
6. Move validated files to `Validated/` subdirectory

**Hard-Ban Validation**:
- Rejects code containing: `sorry`, `admit`, `axiom`, `partial`, `unsafe`
- Rejects deprecated APIs: `String.get`, `String.Pos`, `Std.HashMap.findD`
- Ensures code can compile without placeholders

### Current Benchmark Structure

`TacticsGeneration/Benchmark.lean` contains 10 manually coded reference tasks:
- **Dynamic programming**: min cost path, domino tilings
- **Set operations**: shared elements using HashSet
- **Number theory**: primality checking
- **Heap algorithms**: k-largest/smallest elements
- **String manipulation**: rotation detection, word filtering
- **List operations**: mapping, filtering

Each benchmark task includes:
- Problem description as doc comment
- Implementation code
- `#guard` test assertions

`Test*.lean` files document experimental iterations with LLM feedback annotations.

**Future**: Benchmarks will evolve to include mathematical theorems from various domains (algebra, analysis, combinatorics, number theory, etc.).

## Important Conventions

### Lean Code Style (Current Implementation)

**For Batteries/Std-only code** (current constraint):
- First two lines: `import Batteries` and `open Std`
- Imperative style: `Id.run do`, mutable arrays, for loops
- Prefer `Array` over `List` for indexed operations
- Use `HashSet.ofList` and `HashSet.filter` for set operations
- Never use sorting functions for set operations (compare as HashSets)
- String indexing: convert to `List Char` via `.data`, manipulate, then `String.mk`

**For mathematical formalization** (future):
- Use Mathlib imports as needed: `import Mathlib.Algebra.Ring.Basic`, etc.
- Leverage existing tactics: `simp`, `ring`, `linarith`, `omega`, `aesop`
- Follow Mathlib style: snake_case for definitions, CamelCase for types
- Use type classes for algebraic structures
- Prefer `calc` blocks for equational reasoning
- Add doc comments (`/--` ... `-/`) for theorems and definitions

### File and Module Naming

**Current system:**
- Task IDs from `task_id` field in input JSONL
- Generated files: `Task{id}.lean` (e.g., `Task123.lean`)
- Module name matches filename: `Task123`
- `convert_to_lean.py` tracks processed task_ids to avoid reprocessing

**Future evolution:**
- Theorem files: descriptive names (e.g., `FermatsLittleTheorem.lean`)
- Organized by mathematical domain (e.g., `NumberTheory/`, `Algebra/`)
- Module hierarchy reflecting mathematical structure

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

### LLM Code Generation Issues

If code generation or repair consistently fails:
- **API Key**: Check `openai_key.txt` is present at project root and valid
- **Few-shot examples**: Verify examples in `prompts/few_shots.txt` follow current constraints
- **Repair rounds**: Increase `--max-repair-rounds` in `fix_lean.py` (default: 4)
- **Model availability**: Verify model name in `--model` flag (e.g., `gpt-5`)
- **Prompt templates**: Check all prompt files exist in `prompts/` directory

### Script Execution Issues

**Important**: Always use `python3` instead of `python`:
- ✅ Correct: `python3 scripts/fix_lean.py ...`
- ❌ Wrong: `python scripts/fix_lean.py ...`

Scripts must be run from project root, not from `scripts/` directory:
- ✅ Correct: `python3 scripts/convert_to_lean.py ...` (from project root)
- ❌ Wrong: `cd scripts && python3 convert_to_lean.py ...`

### Path Resolution

Scripts automatically resolve paths relative to project root:
- `prompts/` → looked up from project root
- `openai_key.txt` → looked up from project root
- Input/output files → interpreted relative to current directory (usually project root)

## Technical Implementation Notes

### File Generation (`write_lean_from_entry.py`)

- Merges imports from code and tests (deduplicates, preserves order)
- Adds auto-generated header: `/-! Auto-generated from task {id}. Module: Task{id} -/`
- Structures file: imports → header → code → `-- Tests` → tests
- Returns `Path` object for generated file

### Repair System (`fix_lean.py`)

- Detects Lake project root by searching for `lakefile.lean` or `lake-manifest.json`
- Uses `lake env lean` for compilation (ensures dependencies available)
- Parses diagnostics from stdout/stderr (format: `file:line:col: error: message`)
- Validates against regex patterns for hard-banned tokens
- Progressively strengthens system prompt on retries

### Prompt Externalization

All prompts stored in `prompts/` for easy modification:
- `convert_system_instructions.txt`: Main translation rules
- `convert_user_template.txt`: Task-specific prompt format
- `fix_system_base.txt`: Repair instructions
- `fix_system_retry_append.txt`: Stricter retry instructions
- `fix_api_hint.txt`: API usage guidance
- `fix_string_idioms_hint.txt`: String handling examples

## Future Development Roadmap

### Planned Multi-Agent Components

**Phase 1: Foundation (Current)**
- ✅ LLM-based code generation infrastructure
- ✅ Iterative repair system with compilation feedback
- ✅ Externalized prompt engineering
- ✅ Validation and hard-ban checking

**Phase 2: Mathematical Formalization**
- 🔲 Natural language theorem parser
- 🔲 Theorem → Lean formalization agent
- 🔲 Mathlib integration (imports, tactics, type classes)
- 🔲 Mathematical domain classification
- 🔲 Proof sketch → formal proof translation

**Phase 3: Automated Proving**
- 🔲 Tactic suggestion system
- 🔲 Proof search with backtracking
- 🔲 Lemma retrieval from knowledge base
- 🔲 Proof strategy selection (by analogy, by domain)
- 🔲 Integration with external provers (SMT solvers, etc.)

**Phase 4: Knowledge Base & Connections**
- 🔲 Indexed repository of formalized theorems
- 🔲 Semantic search over mathematical concepts
- 🔲 Cross-domain connection discovery
- 🔲 Theorem clustering by similarity
- 🔲 Dependency graph visualization

**Phase 5: Multi-Agent Coordination**
- 🔲 Agent communication protocol
- 🔲 Task decomposition and distribution
- 🔲 Collaborative proof construction
- 🔲 Conflict resolution and proof merging
- 🔲 Meta-learning from successful strategies

### Design Principles

1. **Modularity**: Each agent operates independently with clear interfaces
2. **Extensibility**: New agents can be added without modifying existing ones
3. **Observability**: All agent actions logged for analysis and debugging
4. **Iterativity**: Incremental development with continuous validation
5. **Human-in-loop**: Support for human guidance and feedback

### Contributing

When adding new components:
- Place Python scripts in `scripts/`
- Externalize prompts to `prompts/`
- Use `PROJECT_ROOT` for path resolution
- Add documentation to this file
- Include examples and test cases
- Follow existing code style (type hints, docstrings)

### Phase Completion Protocol

**After completing each implementation phase:**

1. **Provide a clear summary** explaining:
   - What was built (components, files, data)
   - Why design decisions were made
   - How it fits into the larger system
   - What the current state enables

2. **Update documentation**:
   - Add phase completion notes to relevant docs
   - Update architecture diagrams if needed
   - Document any deviations from the original plan

3. **Verify completeness**:
   - All tests passing
   - Code committed (if using git)
   - Dependencies documented
   - Known limitations noted

4. **Pause for user feedback** before proceeding to next phase:
   - User may want to adjust direction
   - User may want to test the current functionality
   - User may have questions about implementation

**This ensures incremental progress with full understanding and alignment at each step.**

---

**Last Updated**: This is an evolving document. Update as the project develops.