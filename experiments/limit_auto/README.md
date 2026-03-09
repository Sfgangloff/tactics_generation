# limit_auto — 2×2 Study

This directory contains the four experimental conditions for the `limit_auto` tactic,
which automatically proves `Tendsto f F G` goals in Lean 4 / Mathlib.

## Study design

|                    | No milestone plan          | With milestone plan       |
|--------------------|----------------------------|---------------------------|
| **No LSP tools**   | A: `one_run/` (empty)      | B: `plan_without_lsp/`    |
| **With LSP tools** | C: `one_shot_with_lsp/`    | D: `plan_with_lsp/` (best)|

- **A** (no plan, no LSP): raw one-shot API call — produced no usable output.
- **B** (plan, no LSP): milestone plan generated first, implemented via API without
  compiler feedback. Compiles but several tests fail due to wrong Mathlib lemma names.
- **C** (no plan + LSP): one-shot implementation using Claude Code with live LSP feedback.
  Zero errors, all tests pass after iterative repair.
- **D** (plan + LSP): full 9-milestone evolution with LSP feedback at each step.
  Zero errors, richest test suite, most readable architecture.

## Files

- `spec.md` — the tactic specification generated from a one-line user request
- `plan_with_lsp/` — condition D: plan.md + milestone1..9.lean + lsp_log.md
- `plan_without_lsp/` — condition B: plan.md + milestone1..5.lean
- `one_shot_with_lsp/` — condition C: output.lean
