# CLAUDE.md

Lean 4 tactic generation pipeline using LLMs.

## Commands

```bash
# Lean
lake update
lake build

# Python
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt

# Single tactic
python pipeline/main.py "tactic description"
python pipeline/main.py --provider openrouter --model google/gemini-pro "tactic description"

# Batch mode (from specifications.json)
python pipeline/main.py --batch pipeline/specifications.json
python pipeline/main.py --batch pipeline/specifications.json --only Tendsto Nonzero
python pipeline/main.py --batch pipeline/specifications.json --skip RewriteAC --report results.json

# Update mode (add tests to existing tactic)
python pipeline/main.py --update output/my_tactic.lean
python pipeline/main.py --update output/my_tactic.lean --add-tests 10
```

## Structure

```
experiments/        # All experiment data (paper evidence)
├── intuitionistic_pilot/   # pilot experiment
│   └── formula_enumeration/ # Julia formula enumeration (pilot background)
├── limit_auto/             # 2×2 study (main paper contribution)
└── other_tactics/          # future work

pipeline/           # Python pipeline code + CLI
├── main.py        # CLI entry point
├── specifications.json # Tactic descriptions for batch mode
├── models/        # LLM providers (Anthropic, OpenAI, OpenRouter)
├── prompts/       # Prompt templates
├── generator.py   # Orchestrator
├── validator.py   # Lake compilation
├── config.py      # Configuration
└── legacy/        # Earlier pipeline iterations (reference only)

paper/              # Paper draft and plan
output/            # Generated tactics (gitignored, local only)
```

## Configuration

- `--provider anthropic|openai|openrouter` - LLM provider
- `--model NAME` - Specific model (for OpenRouter: e.g., `google/gemini-pro`, `meta-llama/llama-3-70b-instruct`)
- `--mathlib` - Enable Mathlib imports
- `--max-rounds N` - Repair attempts

### Batch Mode Options

- `--batch FILE` - Run batch mode with specifications JSON
- `--only NAME [NAME...]` - Only process these specifications
- `--skip NAME [NAME...]` - Skip these specifications
- `--report FILE` - Write JSON report

### Update Mode Options

- `--update FILE` - Update an existing tactic file
- `--add-tests N` - Number of new tests to add (default: 5)

## Documentation Updates

**Important**: When modifying the codebase (adding features, changing behavior, etc.), always update:

1. **README.md** - Update usage examples, project structure, and pipeline flow as relevant
2. **paper/main.tex** - Update the paper to reflect architectural changes, new features, or design decisions

This ensures documentation stays synchronized with the implementation.
