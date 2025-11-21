# Tactic File Repair Tool

## Overview

`fix_tactic_file.py` is an iterative repair system for Lean 4 tactic files. It automatically:

1. Runs the Lean file through the compiler to detect errors
2. Sends the file content and error diagnostics to OpenAI
3. Receives a corrected version of the file
4. Tests the corrected version
5. Repeats until the file compiles or max iterations is reached

## Usage

### Basic Usage

```bash
python3 scripts/fix_tactic_file.py TacticsGeneration/Tactics/propositions_4_1.lean
```

This will:
- Run up to 5 repair iterations (default)
- Fix errors (warnings are allowed by default)
- Overwrite the file with corrected versions after each iteration
- Stop when the file compiles successfully

### Advanced Options

**Custom iteration limit:**
```bash
python3 scripts/fix_tactic_file.py --max-iterations 10 TacticsGeneration/Tactics/propositions_4_1.lean
```

**Treat warnings as errors (fix both):**
```bash
python3 scripts/fix_tactic_file.py --treat-warnings-as-errors TacticsGeneration/Tactics/propositions_4_1.lean
```

**Allow warnings explicitly:**
```bash
python3 scripts/fix_tactic_file.py --allow-warnings TacticsGeneration/Tactics/propositions_4_1.lean
```

## How It Works

### Architecture

```
┌─────────────────┐
│  Lean Tactic    │
│      File       │
└────────┬────────┘
         │
         ↓
┌─────────────────┐
│  lake env lean  │  ← Check for errors
│   (compiler)    │
└────────┬────────┘
         │
         ↓ (errors found)
┌─────────────────┐
│    OpenAI API   │  ← Send file + errors
│   (gpt-5)       │  ← Get corrected code
└────────┬────────┘
         │
         ↓
┌─────────────────┐
│  Write & Test   │  ← Save corrected file
│                 │  ← Check again
└────────┬────────┘
         │
         ↓ (repeat if errors remain)
    ┌────┴────┐
    │ Success │  or  │ Max iterations │
    └─────────┘      └───────────────┘
```

### Key Features

1. **No dataset dependency**: Unlike `fix_lean.py`, this tool doesn't require a JSONL dataset - it works directly with standalone Lean files

2. **Tactic-aware prompts**: The system prompt (`prompts/fix_tactic_system.txt`) is specifically designed for Lean meta-programming and tactic repair

3. **Iterative refinement**: Each iteration uses the previous errors to guide the next fix attempt

4. **File overwriting**: The tool modifies the file in-place, so make sure to have backups or use version control

5. **Bounded iterations**: Prevents infinite loops by limiting the number of repair attempts

## Prerequisites

### 1. OpenAI API Key

The tool requires an OpenAI API key with access to the `gpt-5` model.

**Option A: File-based (recommended)**
```bash
echo "your-api-key-here" > openai_key.txt
```

**Option B: Environment variable**
```bash
export OPENAI_API_KEY="your-api-key-here"
```

### 2. Lake & Lean 4

Ensure you have:
- Lean 4 installed and on PATH
- Lake (Lean's build tool) installed
- The project built: `lake build`

### 3. Python Dependencies

Install required Python packages:
```bash
pip install openai
```

## Output Examples

### Successful Repair

```
[fix_tactic_file] Checking: TacticsGeneration/Tactics/propositions_4_1.lean
[fix_tactic_file] Found 6 blocking diagnostic(s).
[fix_tactic_file] Starting repair with max 5 iteration(s)...

[fix_tactic_file] === Iteration 1/5 ===
[fix_tactic_file] Calling OpenAI (gpt-5)...
[fix_tactic_file] Wrote candidate code. Checking with Lean...
[fix_tactic_file] Still 3 blocking diagnostic(s) remaining.
  1. [error] line 80: Invalid `⟨...⟩` notation...
  2. [error] line 96: Invalid `⟨...⟩` notation...
  3. [error] line 101: failed to prove index is valid...

[fix_tactic_file] === Iteration 2/5 ===
[fix_tactic_file] Calling OpenAI (gpt-5)...
[fix_tactic_file] Wrote candidate code. Checking with Lean...
[fix_tactic_file] ✓ Success! File compiles cleanly (no errors, no warnings).
```

### Failed Repair

```
[fix_tactic_file] Checking: TacticsGeneration/Tactics/propositions_4_1.lean
[fix_tactic_file] Found 6 blocking diagnostic(s).
[fix_tactic_file] Starting repair with max 5 iteration(s)...

[... iterations ...]

[fix_tactic_file] ✗ Failed to repair after 5 iteration(s).
[fix_tactic_file] Final status: 2 blocking diagnostic(s):
  1. [error] line 80: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
  2. [error] line 96: failed to prove index is valid...
```

## Comparison with `fix_lean.py`

| Feature | `fix_tactic_file.py` | `fix_lean.py` |
|---------|---------------------|---------------|
| Target files | Tactic files with meta-programming | Generated task files |
| Dataset required | No | Yes (JSONL) |
| Python reference | No | Yes |
| Task ID extraction | No | Yes |
| Import style | `import Lean` | `import Batteries` |
| Hard-ban validation | No | Yes (`sorry`, deprecated APIs) |
| Auto-move to Validated/ | No | Yes |
| Default max iterations | 5 | 4 |

## Prompt Engineering

The system prompt is located at:
```
prompts/fix_tactic_system.txt
```

Key aspects of the prompt:
- Guides OpenAI to understand Lean 4 meta-programming
- Explains common tactic file issues (type mismatches, monad issues, etc.)
- Emphasizes returning only complete, working code
- Prohibits placeholders like `sorry`

You can modify this prompt to:
- Add domain-specific guidance
- Include examples of common fixes
- Adjust the repair strategy

## Troubleshooting

### "Command 'lake' not found"

Ensure Lake is installed and on your PATH:
```bash
which lake  # Should show lake's location
```

### "No OpenAI API key found"

Create `openai_key.txt` in the project root or set `OPENAI_API_KEY` environment variable.

### "Lean compilation timed out"

Large files may take longer to compile. The default timeout is 300 seconds (5 minutes). If needed, you can modify the timeout in the script.

### File gets corrupted during repair

Always keep a backup before running the repair tool:
```bash
cp TacticsGeneration/Tactics/propositions_4_1.lean TacticsGeneration/Tactics/propositions_4_1.lean.backup
python3 scripts/fix_tactic_file.py TacticsGeneration/Tactics/propositions_4_1.lean
```

Or use git to track changes:
```bash
git add TacticsGeneration/Tactics/propositions_4_1.lean
git commit -m "Before repair"
python3 scripts/fix_tactic_file.py TacticsGeneration/Tactics/propositions_4_1.lean
git diff  # See what changed
```

## Integration with Workflow

### Batch Repair Multiple Files

```bash
#!/bin/bash
for file in TacticsGeneration/Tactics/*.lean; do
  echo "Processing $file..."
  python3 scripts/fix_tactic_file.py "$file"
done
```

### CI/CD Integration

```bash
# Check if file compiles, attempt repair if not
python3 scripts/fix_tactic_file.py TacticsGeneration/Tactics/propositions_4_1.lean
if [ $? -ne 0 ]; then
  echo "Repair failed"
  exit 1
fi
```

## Limitations

1. **API Costs**: Each iteration calls OpenAI's API, which incurs costs
2. **Model limitations**: GPT-5 may not understand complex Lean meta-programming patterns
3. **No guarantee**: Complex errors may not be fixable automatically
4. **File overwriting**: The tool modifies files in-place - use version control
5. **Timeout**: Very large files may timeout during compilation

## Future Enhancements

Possible improvements:
- Support for custom models (e.g., Claude, local LLMs)
- Dry-run mode (preview fixes without writing)
- Diff output (show what changed)
- Parallel batch processing
- Learning from successful repairs (few-shot examples)
- Integration with Lean LSP for better error context

## License

This tool is part of the tactics_generation project.
