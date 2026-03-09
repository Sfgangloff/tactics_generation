# limit_auto — 2×2 Study

This directory contains the four experimental conditions for the `limit_auto` tactic,
which automatically proves `Tendsto f F G` goals in Lean 4 / Mathlib.

## Study design

|                    | No milestone plan          | With milestone plan       |
|--------------------|----------------------------|---------------------------|
| **No LSP tools**   | A: `one_run/` (empty)      | B: `plan_without_lsp/`    |
| **With LSP tools** | C: `one_shot_with_lsp/`    | D: `plan_with_lsp/` (best)|

## How each condition was run

**Condition A** (`one_run/`) — run via the **automated pipeline** (`pipeline/main.py`):
the pipeline made a single API call to generate the tactic, then ran an automated
self-correction loop feeding compiler errors back to the model. Produced no usable output.
Note: the failure is ambiguous — it could be attributable to the pipeline scaffolding,
the model, or both.

**Condition B** (`plan_without_lsp/`) — run interactively in **Claude Code**, without
live LSP access. The shared `spec.md` and a hand-written milestone plan (`plan.md`) were
fed to the model, which was asked to implement each milestone in sequence. At each step
the previous milestone Lean file and the plan were provided as context, but the model had
no access to the live Lean compiler. Compiles, but several tests fail due to wrong Mathlib
lemma names.

**Condition C** (`one_shot_with_lsp/`) — run interactively in **Claude Code** with live
LSP tools enabled. The model was given only the `spec.md` specification and asked to
implement the tactic in a single session, using LSP tools to query the Lean compiler
and Mathlib as needed. Zero errors, all tests pass.

**Condition D** (`plan_with_lsp/`) — run interactively in **Claude Code** with live LSP
tools enabled. The model was given the `spec.md` and a milestone plan (`plan.md`) and
asked to implement milestones one by one, feeding back the previous milestone file and
the plan at each step. Full access to LSP throughout. Zero errors, richest test suite,
most readable architecture.

## Files

- `spec.md` — the tactic specification (generated from a one-line user request by the pipeline's `analyze_request` stage)
- `one_run/` — condition A: `limit_auto.one_run.lean` (pipeline output)
- `plan_without_lsp/` — condition B: `plan.md` + `milestone1.lean` … `milestone5.lean`
- `one_shot_with_lsp/` — condition C: `output.lean`
- `plan_with_lsp/` — condition D: `plan.md` + `milestone1.lean` … `milestone9.lean` + `lsp_log.md`
