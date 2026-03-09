# Pipeline

The Python pipeline generates Lean 4 tactics from informal natural language descriptions.
It corresponds to **Conditions A and B** of the 2×2 study: API-based generation with a
self-correction loop (no live LSP access).

---

## Architecture

```
User request (string)
        │
        ▼
┌─────────────────┐
│  1. Analyze     │  analyze_request.txt  →  structured spec (TacticSpec)
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  2. Test Algo   │  generate_test_algorithm.txt  →  test enumeration strategy
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  3. Generate    │  generate_tactic.txt  →  Lean 4 metaprogramming code
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  4. Tests       │  generate_tests.txt  →  N theorem statements
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  5. Validate    │  lake env lean <file>  →  errors / success
└────────┬────────┘
         │
    ┌────┴────┐
    │ errors? │
    └────┬────┘
    yes  │  no
         │   └──→  save .lean + .spec.md  →  done
         ▼
┌─────────────────┐
│  6. Repair      │  fix_errors.txt  →  corrected code  (up to N rounds)
└────────┬────────┘
         └──→  back to Validate
```

**Note**: Conditions C and D of the study use Claude Code with live LSP tools instead
of this pipeline. The pipeline implements the non-LSP path (A and B).

---

## Files

### Core

| File | Role |
|------|------|
| `generator.py` | Orchestrator — runs the 6-stage pipeline, handles single/batch/update modes |
| `validator.py` | Calls `lake env lean` on a temp file, parses errors and warnings |
| `config.py` | `Config` dataclass: provider, model, mathlib flag, repair rounds, output dir |

### Models (`models/`)

Abstract interface `LLMModel` with three implementations:

| File | Provider | Default model |
|------|----------|---------------|
| `anthropic_model.py` | Anthropic API | `claude-sonnet-4-20250514` |
| `openai_model.py` | OpenAI API | `gpt-4o` |
| `openrouter_model.py` | OpenRouter | configurable (Gemini, Llama, …) |

API keys are read from environment variables (`ANTHROPIC_API_KEY` etc.) or from
`anthropic_key.txt` / `openai_key.txt` / `openrouter_key.txt` files in the project root
(auto-gitignored).

### Prompts (`prompts/`)

Each prompt is a plain-text template loaded at runtime:

| File | Stage | Purpose |
|------|-------|---------|
| `analyze_request.txt` | 1 | Extract structured spec from informal description |
| `generate_test_algorithm.txt` | 2 | Describe how to enumerate test cases systematically |
| `generate_tactic.txt` | 3 | Generate Lean 4 metaprogramming code |
| `generate_tests.txt` | 4 | Instantiate N test theorems from the algorithm |
| `fix_errors.txt` | 6 | Repair code given compiler error messages |
| `generate_additional_tests.txt` | update | Generate new tests without duplicating existing ones |
| `update_tactic.txt` | update | Extend tactic to handle new test cases |
| `split_specifications.txt` | batch | Detect if one spec describes multiple tactics |

---

## Usage

```bash
# Single tactic
python main.py "description"
python main.py --mathlib --provider anthropic "description"
python main.py --provider openrouter --model google/gemini-pro "description"

# Batch (from specifications.json)
python main.py --batch specifications.json --mathlib
python main.py --batch specifications.json --only TacticA TacticB
python main.py --batch specifications.json --report results.json

# Update existing tactic
python main.py --update output/my_tactic.lean
python main.py --update output/my_tactic.lean --add-tests 10 --max-rounds 6
```

---

## Legacy (`legacy/`)

See [`legacy/README.md`](legacy/README.md) for documentation of earlier pipeline
iterations kept for historical reference.
