# Pipeline

The pipeline generates two preparation artefacts from an informal tactic description:
a structured **specification** and an incremental **milestone plan**. These are used
to prepare Claude Code sessions for the 2×2 study (Conditions B and D).

The pipeline does **not** attempt to compile or implement tactics. All interactive
work — writing Lean code, calling LSP tools, fixing errors — happens inside Claude Code.

---

## What the pipeline produces

For each tactic description, the pipeline writes two files to `output/`:

| File | Content |
|------|---------|
| `{name}.spec.md` | Structured spec: name, scope analysis, mathematical characterisation, algorithm, success criteria, edge cases, dependencies |
| `{name}.plan.md` | Incremental milestone plan: 8–12 milestones, each with new capability, example Lean goals, key Mathlib lemmas, and implementation notes |

---

## Architecture

```
User request (string)
        │
        ▼
┌─────────────────┐
│  1. Analyze     │  analyze_request.txt  →  structured spec
└────────┬────────┘
         │  save  →  output/{name}.spec.md
         ▼
┌─────────────────┐
│  2. Plan        │  generate_plan.txt  →  milestone plan
└────────┬────────┘
         │  save  →  output/{name}.plan.md
         ▼
        done
```

Two LLM calls total. No Lean compilation.

---

## Files

### Core

| File | Role |
|------|------|
| `generator.py` | Orchestrator — runs the 2-stage pipeline, handles single and batch modes |
| `config.py` | `Config` dataclass: provider, model, output dir |

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

| File | Stage | Purpose |
|------|-------|---------|
| `analyze_request.txt` | 1 | Extract structured spec from informal description |
| `generate_plan.txt` | 2 | Generate incremental milestone plan from spec |
| `split_specifications.txt` | batch | Detect if one spec describes multiple tactics |

---

## Usage

```bash
# Single tactic
python pipeline/main.py "A tactic that proves nonzero goals"
python pipeline/main.py --provider anthropic "..."
python pipeline/main.py --provider openrouter --model google/gemini-pro "..."
python pipeline/main.py -f request.txt

# Batch (from specifications.json)
python pipeline/main.py --batch pipeline/specifications.json
python pipeline/main.py --batch pipeline/specifications.json --only TacticA TacticB
python pipeline/main.py --batch pipeline/specifications.json --skip RewriteAC
```

---

## Legacy (`legacy/`)

See [`legacy/README.md`](legacy/README.md) for documentation of earlier pipeline
iterations kept for historical reference.
