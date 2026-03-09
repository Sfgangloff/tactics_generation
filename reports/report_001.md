# Report T01 — Quantitative comparison table

## What was done

Added Table 2 (`tab:results`) to `paper/main.tex`, immediately before the
"Results per Condition" paragraph breakdowns (§4.4).

## Data collected

Metrics were read directly from the experiment files:

| Condition | Source file | LOC | Tests (^theorem/^example) |
|-----------|------------|-----|--------------------------|
| A | `experiments/limit_auto/one_run/limit_auto.one_run.lean` | 0 | 0 |
| B | `experiments/limit_auto/plan_without_lsp/milestone5.lean` | 160 | 9 |
| C | `experiments/limit_auto/one_shot_with_lsp/output.lean` | 307 | 17 |
| D | `experiments/limit_auto/plan_with_lsp/milestone9.lean` | 325 | 16 |

- **Tests pass**: Condition B has 1 failing test (`exp(-1/x)` example marked with
  `#guard_msgs` confirming failure). All others pass.
- **LSP calls**: Condition D count (34) from `experiments/limit_auto/plan_with_lsp/lsp_log.md`.
  Condition C used LSP interactively without a separate call log.
- **Milestones**: Counted from files in each condition directory.

## Why

The 2×2 study was entirely qualitative. A quantitative table is the minimum
required for a credible conference submission and directly addresses the open
`\comment{}` on line 115 of the paper about how to compare conditions.
