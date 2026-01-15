# Tactics Generation

A pipeline for generating Lean 4 tactics from informal natural language descriptions using LLMs.

## Prerequisites

- Lean 4 with Lake ([installation guide](https://leanprover.github.io/lean4/doc/setup.html))
- Python 3.10+
- API key for Anthropic or OpenAI

## Setup

```bash
# Setup Lean project
lake update
lake build

# Setup Python environment
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

# Set API key
export ANTHROPIC_API_KEY="your-key-here"
# or
export OPENAI_API_KEY="your-key-here"
```

## Usage

```bash
# Basic usage (Anthropic by default)
python main.py "Create a tactic that simplifies boolean expressions"

# Use OpenAI
python main.py --provider openai "Create a tactic that applies symmetry"

# Enable Mathlib imports
python main.py --mathlib "Create a tactic for finding limits"

# Read request from file
python main.py -f request.txt

# More options
python main.py --help
```

## Project Structure

```
tactics_generation/
├── pipeline/              # Python pipeline
│   ├── models/           # LLM provider abstraction
│   ├── prompts/          # Prompt templates
│   ├── generator.py      # Main orchestrator
│   ├── validator.py      # Lean compilation
│   └── config.py         # Configuration
├── output/               # Generated tactics
├── main.py               # CLI entry point
├── lakefile.toml         # Lean project config
└── requirements.txt      # Python dependencies
```

## Pipeline Flow

1. **Analyze**: Parse informal request into structured specification
2. **Generate**: Create Lean 4 metaprogramming code
3. **Validate**: Compile with Lake
4. **Repair**: If errors, feed back to LLM (up to N rounds)
5. **Output**: Save validated tactic
