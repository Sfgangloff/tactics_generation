# Report T05 — Error-analysis step in self-correction loop

## What was done

Modified `pipeline/generator.py` (`_repair_code` method) and added a new prompt
`pipeline/prompts/analyze_errors.txt` to implement a two-step self-correction loop
inspired by **Boosting of Thoughts** (Chen et al., arXiv:2402.11140).

### Before
The repair loop sent code + errors directly to the fix prompt and generated a
corrected file in one step. This often produced local fixes that didn't address
the root cause (e.g. fixing a syntax error while missing that the underlying
approach was wrong).

### After
The repair loop now runs two model calls per repair round:
1. **Diagnosis call** (`analyze_errors.txt`): asks the model to explain the root
   cause of each error and identify any strategy change needed. No code is written.
2. **Fix call** (`fix_errors.txt`): generates the corrected code, with the diagnosis
   appended as additional context.

The diagnosis step costs one extra LLM call per repair round but gives the model an
explicit "think before you fix" phase, which matches the BoT finding that error
analysis improves subsequent repairs.

## Files changed

- `pipeline/generator.py`: `_repair_code` method (added diagnosis step + prompt load)
- `pipeline/prompts/analyze_errors.txt`: new prompt (diagnosis only, no code output)

## Why

The self-correction loop in Conditions A/B is the main pipeline mechanism for
handling errors. The current loop treats each repair round identically; BoT shows
that an explicit error-analysis step before repair significantly improves convergence.
This change makes Condition A/B more likely to succeed on future tactic targets
and directly addresses item §9 "Better self-correction" in suggestions.md.
