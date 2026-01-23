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

### Single Tactic Generation

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

### Batch Mode

Process multiple specifications from a JSON file. Specifications that describe multiple tactics are automatically split into individual tactic generations.

```bash
# Process all specifications
python main.py --batch specifications.json --mathlib

# Process specific specifications only
python main.py --batch specifications.json --only Tendsto Nonzero

# Skip certain specifications
python main.py --batch specifications.json --skip RewriteAC

# Generate a JSON report
python main.py --batch specifications.json --report results.json
```

The `specifications.json` file format:
```json
{
  "TacticName": {
    "description": "Informal description of the tactic..."
  }
}
```

When a specification describes multiple distinct tactics (e.g., "compute equality, coefficient, and leading term for polynomials"), the pipeline automatically splits it into separate tactic generations.

### Update Mode

Incrementally improve an existing tactic by adding new test cases and updating the implementation to handle them.

```bash
# Add 5 new tests to an existing tactic (default)
python main.py --update output/my_tactic.lean

# Add a specific number of tests
python main.py --update output/my_tactic.lean --add-tests 10

# With increased repair rounds for complex updates
python main.py --update output/my_tactic.lean --add-tests 10 --max-rounds 6
```

Requirements for update mode:
- The `.lean` file must exist
- A corresponding `.spec.md` file must exist (created during initial generation)

The update pipeline:
1. Parses the existing specification and test algorithm
2. Generates new non-duplicate tests following the same algorithm
3. Appends tests to the file
4. Updates the tactic implementation if needed (via repair loop)

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
├── batch_run.py          # Standalone batch runner
├── specifications.json   # User specifications for batch mode
├── lakefile.toml         # Lean project config
└── requirements.txt      # Python dependencies
```

## Pipeline Flow

### Single Tactic Mode
1. **Analyze**: Parse informal request into structured specification
2. **Test Algorithm**: Generate systematic test generation strategy
3. **Generate Tactic**: Create Lean 4 metaprogramming code
4. **Generate Tests**: Create test theorems using the algorithm
5. **Validate**: Compile with Lake
6. **Repair**: If errors, feed back to LLM (up to N rounds)
7. **Output**: Save validated tactic and specification

### Batch Mode
1. **Load**: Read specifications from JSON file
2. **Split**: For each specification, identify if it describes multiple tactics
3. **Generate**: For each individual tactic specification, run the single tactic pipeline
4. **Report**: Aggregate results and optionally write JSON report

### Update Mode
1. **Load**: Read existing tactic and specification files
2. **Generate Additional Tests**: Create new non-duplicate tests using the original algorithm
3. **Append**: Add new tests to the file
4. **Validate & Repair**: Update tactic implementation if tests fail
5. **Save**: Write updated file
