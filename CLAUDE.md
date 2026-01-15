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
python main.py "tactic description"
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
output/            # Generated tactics
```

## Configuration

- `--provider anthropic|openai` - LLM provider
- `--model NAME` - Specific model
- `--mathlib` - Enable Mathlib imports
- `--max-rounds N` - Repair attempts
