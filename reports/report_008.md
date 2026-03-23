# Report 008 — decide_list_theory Condition A: No Plan, No LSP

**Date**: 2026-03-11
**Tactic**: `decide_list_theory`
**Condition**: A — no milestone plan, no LSP tools

---

## Result

**Failed to compile. 0 / 18 tests pass.**

---

## Errors

Three syntax errors prevent tactic registration:

| Line | Error |
|------|-------|
| 64 | `invalid use of (<- ...), must be nested inside a 'do' expression` |
| 80 | Same — second `evalTactic` helper defined outside `do` |
| 97 | `unexpected token '*'; expected ')'` — from `` `(tactic| intro *) `` |

Because `elab "decide_list_theory" : tactic` references `decideListTheoryImpl`,
which depends on the broken helpers, the tactic is never registered. All 18 test
cases report "unknown tactic" and leave goals unsolved.

---

## What the model produced

The model generated a complete 183-line implementation (plus 18-test suite)
in a single pass. The design is reasonable:

- `tryTac` helper for rollback-on-failure
- `listNormalizeTac` and `listFullSimpTac` using `simp only` / `simp`
- 11-step waterfall: `rfl`, `decide`, `omega`, `tauto`, `fullSimp`,
  normalize+`omega`, normalize+`tauto`, normalize+`decide`,
  normalize+multi-solver, fullSimp+`omega`, fullSimp+`tauto`, `aesop`
- 18 test cases covering append laws, length arithmetic, membership, logic

The structure is architecturally sound. The errors are shallow Lean 4
metaprogramming syntax mistakes that would be caught instantly by LSP:

- `evalTactic (← ...)` requires a `do` block; using it directly in a `let`
  binding at the top level of a non-`do` definition is invalid.
- `` `(tactic| intro *) `` — the `*` in `intro *` is not valid quoted tactic
  syntax in this Lean version; should be `` `(tactic| intro) `` or handled
  differently.

---

## Comparison

| Condition | Plan | LSP | Outcome |
|-----------|------|-----|---------|
| A         | No   | No  | **0 / 18 tests** — 3 syntax errors, tactic unregistered |
| B         | Yes  | No  | not run |
| C         | No   | Yes | not run |
| D         | Yes  | Yes | all milestones complete ✓ |

---

## Interpretation

Condition A fails for `decide_list_theory` for the same reason it fails for
`limit_auto`: without LSP diagnostics the model cannot detect shallow syntax
errors and does not attempt repair. The errors are of the kind that the LSP
would surface within one round-trip, so Condition C (no plan, with LSP) is
the natural comparison.
