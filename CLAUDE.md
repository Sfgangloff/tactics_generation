# CLAUDE.md

Research project: LLM-assisted Lean 4 tactic generation.
Paper: *Generating Lean 4 Tactics from User Specifications* (ITP short paper).

## Project Layout

```
paper/              # LaTeX draft (main.tex) and section plan
experiments/        # All experimental evidence for the paper
  intuitionistic_pilot/  # Pilot: three approaches to tactic generation
  limit_auto/            # 2×2 study (main contribution)
  other_tactics/         # decide_list_theory + 12 draft specs
pipeline/           # Automated generation pipeline (Python)
  main.py            # CLI entry point
  specifications.json
  generator.py / validator.py / config.py
  models/ prompts/ legacy/
```

## Documentation Updates

When modifying the codebase, always keep in sync:
1. **README.md** — project overview and structure
2. **paper/main.tex** — paper draft (reflect any design decisions)
3. **experiments/*/README.md** — experiment-level documentation

## Lean Commands

```bash
lake update
lake build
```

## Pipeline Commands (run from project root)

```bash
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt

# Single tactic
python pipeline/main.py "tactic description"
python pipeline/main.py --provider openrouter --model google/gemini-pro "tactic description"

# Batch mode
python pipeline/main.py --batch pipeline/specifications.json
python pipeline/main.py --batch pipeline/specifications.json --only Tendsto Nonzero
python pipeline/main.py --batch pipeline/specifications.json --skip RewriteAC --report results.json

# Update mode (add tests to existing tactic)
python pipeline/main.py --update output/my_tactic.lean
python pipeline/main.py --update output/my_tactic.lean --add-tests 10
```

## Pipeline Configuration

- `--provider anthropic|openai|openrouter`
- `--model NAME` (e.g. `google/gemini-pro`, `meta-llama/llama-3-70b-instruct`)
- `--mathlib` — enable Mathlib imports
- `--max-rounds N` — repair attempts
- `--batch FILE` / `--only` / `--skip` / `--report FILE`
- `--update FILE` / `--add-tests N`
