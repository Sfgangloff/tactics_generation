# Session Brief — Condition E: No Plan, No LSP (Interactive)

**Purpose**: Disambiguate Condition A's failure. Condition A was run via the automated
pipeline. This session runs the same task interactively in Claude Code but with the
same constraints (no plan, no LSP tools), to determine whether the failure was due to
the pipeline scaffolding or the absence of structural guidance.

---

## Setup

- Open a **fresh Claude Code session** in the project root
- **Do not** write a milestone plan before starting
- **Do not** use any LSP tools (`lean_goal`, `lean_diagnostic_messages`,
  `lean_leansearch`, `lean_loogle`, `lean_local_search`, `lean_multi_attempt`, etc.)
- You may use the compiler only by running `lake build` via Bash if needed,
  but do not use the LSP tool suite

---

## Prompt to give the model

Paste the following as your first message:

---

I want you to implement a Lean 4 tactic called `limit_auto` from the specification
below. Do not write a milestone plan — implement the full tactic in one session.
Do not use any LSP tools (no lean_goal, lean_diagnostic_messages, lean_leansearch, etc.).

Save the output to `experiments/limit_auto/one_shot_no_lsp/output.lean`.

Here is the specification:

[paste the full contents of experiments/limit_auto/spec.md here]

---

## What to record

After the session, save:
- `output.lean` — the final generated file (even if it doesn't compile)
- `notes.md` — brief notes on what happened: did it produce code? did it compile?
  how many repair attempts? what errors occurred?

---

## Comparison baseline

| Condition | Method | Result |
|-----------|--------|--------|
| A | Automated pipeline (no plan, no LSP) | Empty file, no convergence |
| C | Interactive Claude Code (no plan, WITH LSP) | 17/17 tests pass |
| **E** | **Interactive Claude Code (no plan, no LSP)** | **← this session** |

If E also fails or produces wrong lemma names, the failure in A is due to the
absence of LSP, not the pipeline scaffolding. If E succeeds, A's failure was
a pipeline artifact.
