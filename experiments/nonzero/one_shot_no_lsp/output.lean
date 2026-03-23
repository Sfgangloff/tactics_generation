import Mathlib.Tactic
import Mathlib.Tactic.Positivity

/-!
# The `nonzero` tactic

Implements `nonzero`, a tactic for proving goals of the form `e ≠ 0` using structural
algebraic lemmas and `positivity` as a fallback. It is at least as powerful as the
nonzero-proving component used internally by `field_simp`.

## Algorithm

1. `assumption` — check the local context for a matching hypothesis
2. `norm_num` — discharge numeric literal goals (only when it fully closes the goal)
3. `positivity` — handle ordered expressions directly (only when it fully closes the goal)
4. Negation: `-a ≠ 0` from `a ≠ 0` via `neg_ne_zero.mpr`
5. Power: `a ^ n ≠ 0` from `a ≠ 0` via `pow_ne_zero`
6. Multiplication: `a * b ≠ 0` from `a ≠ 0` and `b ≠ 0` via `mul_ne_zero`

All structural strategies are applied recursively with a fuel-bounded depth limit.

## Design Notes

- `pow_ne_zero` is tried before `mul_ne_zero` for efficiency.
- `tryClose` (vs plain `tryT`) is used for `norm_num` and `positivity` to ensure they
  fully close the goal before we accept their success. Without this, `norm_num` may
  partially simplify a goal (e.g., `a ^ 3 ≠ 0` → `¬a = 0`) without closing it,
  causing the tactic to return prematurely with unsolved goals.
-/

open Lean Elab Tactic Meta

/-- Save state; try `t`; restore on failure. Returns `true` iff `t` succeeds. -/
private def tryT (t : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  try
    t
    return true
  catch _ =>
    restoreState saved
    return false

/-- Like `tryT`, but also requires that `t` leaves no remaining goals. -/
private def tryClose (t : TacticM Unit) : TacticM Bool :=
  tryT do
    t
    let goals ← getGoals
    if !goals.isEmpty then throwError "nonzero: tactic did not close the goal"

/-- Core recursive implementation of the `nonzero` tactic.

Tries each strategy with `tryT` backtracking; `pow_ne_zero` is applied before
`mul_ne_zero` so that powers are handled atomically rather than unrolled. -/
private partial def nonzeroImpl (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then throwError "nonzero: maximum recursion depth exceeded"

  -- Base: hypothesis in local context
  if ← tryT (evalTactic (← `(tactic| assumption))) then return

  -- Base: numeric constants (`2 ≠ 0`, `(3 : ℤ) ≠ 0`, etc.)
  -- Use tryClose so that a partial norm_num simplification doesn't fool us.
  if ← tryClose (evalTactic (← `(tactic| norm_num))) then return

  -- Positivity fallback: handles ordered expressions like `a + b ≠ 0` when `0 < a`.
  -- Use tryClose for the same reason as norm_num.
  if ← tryClose (evalTactic (← `(tactic| positivity))) then return

  -- Negation: `-a ≠ 0` → `a ≠ 0`
  if ← tryT (do
      evalTactic (← `(tactic| apply neg_ne_zero.mpr))
      nonzeroImpl (fuel - 1)) then return

  -- Power: `a ^ n ≠ 0` → `a ≠ 0`  (requires `IsReduced`, holds for fields/domains)
  if ← tryT (do
      evalTactic (← `(tactic| apply pow_ne_zero))
      nonzeroImpl (fuel - 1)) then return

  -- Multiplication: `a * b ≠ 0` → `a ≠ 0` and `b ≠ 0`
  if ← tryT (do
      evalTactic (← `(tactic| apply mul_ne_zero))
      nonzeroImpl (fuel - 1)
      nonzeroImpl (fuel - 1)) then return

  throwError "nonzero: could not prove that this expression is nonzero"

/--
`nonzero` proves goals of the form `e ≠ 0`.

It applies the following strategies recursively:
1. Checks the local context for a matching hypothesis (`assumption`)
2. Uses `norm_num` for numeric literals
3. Falls back to `positivity` for ordered expressions (e.g., `a + b ≠ 0` when `0 < a`)
4. Handles negation: `-a ≠ 0` reduces to `a ≠ 0` (via `neg_ne_zero.mpr`)
5. Handles powers: `a ^ n ≠ 0` reduces to `a ≠ 0` (via `pow_ne_zero`)
6. Handles products: `a * b ≠ 0` reduces to `a ≠ 0` and `b ≠ 0` (via `mul_ne_zero`)

The tactic is at least as powerful as the nonzero-proving component of `field_simp`.
-/
elab "nonzero" : tactic => nonzeroImpl 32

-- ============================================================
-- Test Suite
-- ============================================================

section BasicTests

-- T01: Direct hypothesis lookup
example (a : ℝ) (ha : a ≠ 0) : a ≠ 0 := by nonzero

-- T02: Numeric constant (ℝ)
example : (2 : ℝ) ≠ 0 := by nonzero

-- T03: Numeric constant (ℤ)
example : (3 : ℤ) ≠ 0 := by nonzero

-- T04: Negative numeric constant
example : (-2 : ℚ) ≠ 0 := by nonzero

-- T05: Simple negation  (-a ≠ 0)
example (a : ℝ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- T06: Double negation
example (a : ℝ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero

-- T07: Product of two variables
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- T08: Power with literal exponent
example (a : ℝ) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero

-- T09: Power with exponent 1
example (a : ℝ) (ha : a ≠ 0) : a ^ 1 ≠ 0 := by nonzero

-- T10: Power with exponent 2
example (a : ℝ) (ha : a ≠ 0) : a ^ 2 ≠ 0 := by nonzero

-- T11: Power with variable exponent (all n, using IsReduced)
example (a : ℝ) (n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by nonzero

-- T12: Negation of product
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b) ≠ 0 := by nonzero

-- T13: Product of powers
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 2 * b ^ 3 ≠ 0 := by nonzero

-- T14: Power of negation
example (a : ℝ) (ha : a ≠ 0) : (-a) ^ 4 ≠ 0 := by nonzero

-- T15: Negation of power
example (a : ℝ) (ha : a ≠ 0) : -(a ^ 5) ≠ 0 := by nonzero

-- T16: Triple product (left-associated)
example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * b * c ≠ 0 := by nonzero

-- T17: Nested — negation of product of powers
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a ^ 2 * b) ≠ 0 := by nonzero

-- T18: Nested — product of power and power
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 2 * b ^ 3 ≠ 0 := by nonzero

-- T19: Product of variable and numeric constant
example (a : ℝ) (ha : a ≠ 0) : 2 * a ≠ 0 := by nonzero

-- T20: Power of numeric literal
example : (2 : ℚ) ^ 5 ≠ 0 := by nonzero

end BasicTests

section PositivityTests

-- T21: Sum of two positive reals (positivity fallback)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b ≠ 0 := by nonzero

-- T22: Single positive real
example (a : ℝ) (ha : 0 < a) : a ≠ 0 := by nonzero

-- T23: Sum of positive variable and 1
example (a : ℝ) (ha : 0 < a) : a + 1 ≠ 0 := by nonzero

-- T24: Negation of sum of positives (positivity + neg_ne_zero)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : -(a + b) ≠ 0 := by nonzero

-- T25: Nested: negation-of-power times power-of-sum
example (x y : ℝ) (hx : x ≠ 0) (hy : 0 < y) : -(x ^ 2) * (y + 1) ≠ 0 := by nonzero

end PositivityTests

section AbstractAlgebraTests

-- T26: Ring — negation only (no NoZeroDivisors needed)
example {α : Type*} [Ring α] (a : α) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- T27: Ring — double negation
example {α : Type*} [Ring α] (a : α) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero

-- T28: Field — product
example {α : Type*} [Field α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- T29: Field — power
example {α : Type*} [Field α] (a : α) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero

-- T30: Rational number constant
example : (7 : ℚ) ≠ 0 := by nonzero

end AbstractAlgebraTests
