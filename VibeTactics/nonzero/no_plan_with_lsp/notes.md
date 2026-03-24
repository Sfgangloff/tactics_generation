# Session Notes

---

## Identity

| Field | Value |
|-------|-------|
| Tactic | `nonzero` |
| Condition | C |
| Plan | No |
| LSP tools | Yes |
| Date | 2026-03-13 |

---

## Outcome

| Field | Value |
|-------|-------|
| Compiled? | Yes |
| Tests passing / total | 25 / 25 |
| Milestones completed / planned | — (no plan) |
| First milestone that compiled | — (no milestones) |

---

## Effort metrics

| Field | Value |
|-------|-------|
| LOC — implementation body (excl. tests) | 71 |
| LOC — test suite | 78 |
| `lake build` calls | 0 |
| Repair cycles (error → fix iterations) | 7 |

---

## LSP tool usage

| Tool | Calls |
|------|-------|
| `lean_diagnostic_messages` | 16 |
| `lean_goal` | 8 |
| `lean_leansearch` | 2 |
| `lean_loogle` | 4 |
| `lean_leanfinder` | 0 |
| `lean_local_search` | 4 |
| `lean_multi_attempt` | 4 |
| `lean_hover_info` | 3 |
| `lean_state_search` | 0 |
| `lean_hammer_premise` | 0 |
| `lean_completions` | 0 |
| **Total** | **41** |

---

## Per-milestone summary  _(omitted — Condition C)_

---

## Notable failures and errors

1. **`norm_num` partial transformation** — `norm_num` on symbolic goals like `-a ≠ 0` rewrites the goal without closing it and does not throw; `tryT` (exception-based) treated this as success, leaving unsolved goals. Fix: introduced `tryClose` which additionally checks `goals.isEmpty` and rejects partial transformations.

2. **`macro_rules` + `first | (...)` parsing** — `<;>` inside `(...)` inside a `first` combinator escaped the grouping, so `(apply A <;> B)` was parsed as `(apply A) <;> B`. Fix: switched to `elab` with explicit `do`-notation; the issue was moot in the final design.

3. **`Expr.isAppOf` / `whnfR` silent mismatch** — The `elab` implementation with syntactic head inspection (`isAppOf ``Neg.neg` etc.) failed for double-negation, `(-a)^n`, and mixed product/positivity cases, despite the individual lemmas working. Debugging showed `nonzeroSimple` (identical structure but without expression inspection) succeeded. Root cause: `whnfR` or `getAppFn` returned unexpected results for metavariables created by recursive `apply` steps. Fix: removed all `Expr.isAppOf`/`whnfR` logic; each rule is now tried speculatively via `tryT` backtracking.

---

## Free observations

- `lean_diagnostic_messages` was the primary feedback loop throughout; `lake build` was never needed since the LSP provided real-time error information.
- Finding the right lemma names (`neg_ne_zero`, `mul_ne_zero`, `pow_ne_zero` and their precise typeclass requirements) required `lean_loogle` and `lean_local_search`; the typeclass constraints (`NoZeroDivisors`, `IsReduced`, `SubtractionMonoid`) were non-trivial to discover.
- `positivity` required `tryT` (not `tryClose`) since it directly closes `e ≠ 0` goals; `norm_num` required `tryClose` because it can partially rewrite without closing.
- The final design (pure `tryT` backtracking, no Expr inspection) is simpler and more robust than the initial approach. The `pow_ne_zero`-before-`mul_ne_zero` ordering ensures efficient handling of powers without syntactic head checks.
- All 25 tests pass, including generic `Ring` and `Field` type class variants, numeric constants across ℝ/ℤ/ℚ, and deeply nested expressions combining negation, multiplication, power, and positivity.
