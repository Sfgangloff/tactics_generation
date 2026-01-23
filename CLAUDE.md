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
python main.py "tactic description"
python main.py --provider openrouter --model google/gemini-pro "tactic description"

# Batch mode (from specifications.json)
python main.py --batch specifications.json
python main.py --batch specifications.json --only Tendsto Nonzero
python main.py --batch specifications.json --skip RewriteAC --report results.json

# Update mode (add tests to existing tactic)
python main.py --update output/my_tactic.lean
python main.py --update output/my_tactic.lean --add-tests 10
```

## Structure

```
pipeline/           # Python code
├── models/        # LLM providers (Anthropic, OpenAI)
├── prompts/       # Prompt templates
├── generator.py   # Orchestrator
├── validator.py   # Lake compilation
└── config.py      # Configuration

main.py            # CLI entry point
batch_run.py       # Standalone batch runner
specifications.json # User specifications for batch mode
output/            # Generated tactics
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
