import Mathlib.Tactic
import Mathlib.Tactic.Positivity

/-!
# `nonzero` Tactic

A tactic that proves goals of the form `e ≠ 0` using:
1. Algebraic lemmas for negation, multiplication, and power
2. `positivity` as a fallback for ordered algebraic structures

## Implementation

Uses an `elab` tactic with `tryT`-based backtracking. Each structural rule
(`neg_ne_zero.mpr`, `pow_ne_zero`, `mul_ne_zero`) is attempted speculatively:
if `apply` succeeds, the tactic recurses on the resulting subgoals; if it
fails the state is restored and the next rule is tried. No syntactic `Expr`
inspection is used — this avoids subtle bugs where `whnfR` or `getAppFn`
return unexpected results in recursive metavariable contexts.

Note: `pow_ne_zero` is tried before `mul_ne_zero`. If `pow_ne_zero` fails
(e.g., for a product), `mul_ne_zero` fires. If only `mul_ne_zero` applies
to a power (via definitional unification), the fuel limit prevents non-
termination; all exponents in the test suite are ≤ 5, well within fuel=20.

## Strategy
- `assumption`: hypothesis `ha : e ≠ 0` in context
- `norm_num`: numeric constants like `2 ≠ 0`
- `positivity`: ordered structures — sums, etc.
- `neg_ne_zero.mpr`: `-a ≠ 0` from `a ≠ 0`
- `pow_ne_zero`: `a ^ n ≠ 0` from `a ≠ 0`
- `mul_ne_zero`: `a * b ≠ 0` from `a ≠ 0` and `b ≠ 0`
-/

open Lean Elab Tactic Meta

/-- Try `t`; on failure restore state and return `false`. -/
private def tryT (t : TacticM Unit) : TacticM Bool := do
  let saved ← saveState
  try
    t
    return true
  catch _ =>
    restoreState saved
    return false

/-- Try `t`; return `true` only if `t` closes ALL goals (not just transforms them). -/
private def tryClose (t : TacticM Unit) : TacticM Bool :=
  tryT do
    t
    let goals ← getGoals
    if !goals.isEmpty then throwError "tactic did not close the goal"


/-- Core recursive implementation of the `nonzero` tactic.

Tries each strategy with `tryT` backtracking; no syntactic head inspection.
The `pow_ne_zero` rule is tried before `mul_ne_zero` for efficiency (powers
handled in one step rather than unrolling via `mul_ne_zero`). -/
private partial def nonzeroImpl (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then throwError "nonzero: maximum recursion depth exceeded"

  -- Base case: hypothesis in local context
  if ← tryT (evalTactic (← `(tactic| assumption))) then return

  -- Numeric constants: `2 ≠ 0`, `(3 : ℤ) ≠ 0`, etc.
  if ← tryClose (evalTactic (← `(tactic| norm_num))) then return

  -- Positivity: `a + b ≠ 0` when `0 < a`, etc.
  if ← tryT (evalTactic (← `(tactic| positivity))) then return

  -- Negation: `-a ≠ 0` → `a ≠ 0`
  if ← tryT (do
      evalTactic (← `(tactic| apply neg_ne_zero.mpr))
      nonzeroImpl (fuel - 1)) then return

  -- Power: `a ^ n ≠ 0` → `a ≠ 0`
  if ← tryT (do
      evalTactic (← `(tactic| apply pow_ne_zero))
      nonzeroImpl (fuel - 1)) then return

  -- Multiplication: `a * b ≠ 0` → `a ≠ 0` and `b ≠ 0`
  if ← tryT (do
      evalTactic (← `(tactic| apply mul_ne_zero))
      nonzeroImpl (fuel - 1)
      nonzeroImpl (fuel - 1)) then return

  throwError "nonzero: could not prove that expression is nonzero"

/-- Tactic to prove goals of the form `e ≠ 0`.

Applies the following strategies:
- `assumption`: checks local hypotheses for a matching `e ≠ 0`
- `neg_ne_zero.mpr`: proves `-a ≠ 0` from `a ≠ 0`
- `mul_ne_zero`: proves `a * b ≠ 0` from `a ≠ 0` and `b ≠ 0`
- `pow_ne_zero`: proves `a ^ n ≠ 0` from `a ≠ 0` (requires `IsReduced`)
- `norm_num`: proves numeric constants nonzero
- `positivity`: proves `e ≠ 0` in ordered structures

Example:
```lean
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b ^ 2) ≠ 0 := by nonzero
```
-/
elab "nonzero" : tactic => nonzeroImpl 20

/-! ## Test Suite -/

section Tests

-- Test 1: Hypothesis lookup
example (a : ℝ) (ha : a ≠ 0) : a ≠ 0 := by nonzero

-- Test 2: Numeric constant (ℝ)
example : (2 : ℝ) ≠ 0 := by nonzero

-- Test 3: Numeric constant (ℤ)
example : (3 : ℤ) ≠ 0 := by nonzero

-- Test 4: Negation
example (a : ℝ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- Test 5: Double negation
example (a : ℝ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero

-- Test 6: Product
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- Test 7: Power (exponent 3)
example (a : ℝ) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero

-- Test 8: Power (exponent 1)
example (a : ℝ) (ha : a ≠ 0) : a ^ 1 ≠ 0 := by nonzero

-- Test 9: Power (exponent 2)
example (a : ℝ) (ha : a ≠ 0) : a ^ 2 ≠ 0 := by nonzero

-- Test 10: Negation of product
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b) ≠ 0 := by nonzero

-- Test 11: Product of powers
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 2 * b ^ 3 ≠ 0 := by nonzero

-- Test 12: Power of negation
example (a : ℝ) (ha : a ≠ 0) : (-a) ^ 4 ≠ 0 := by nonzero

-- Test 13: Negation of power
example (a : ℝ) (ha : a ≠ 0) : -(a ^ 5) ≠ 0 := by nonzero

-- Test 14: Sum of positives (positivity fallback)
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b ≠ 0 := by nonzero

-- Test 15: Positivity with constant addend
example (a : ℝ) (ha : 0 < a) : a + 1 ≠ 0 := by nonzero

-- Test 16: Nested — negation of product of powers
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a ^ 2 * b) ≠ 0 := by nonzero

-- Test 17: Nested — product of neg-power and positivity
example (x y : ℝ) (hx : x ≠ 0) (hy : 0 < y) : -(x ^ 2) * (y + 1) ≠ 0 := by nonzero

-- Test 18: Three-way product
example (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * b * c ≠ 0 := by nonzero

-- Test 19: Ring — negation only (no NoZeroDivisors needed)
example {α : Type*} [Ring α] (a : α) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- Test 20: Ring — double negation
example {α : Type*} [Ring α] (a : α) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero

-- Test 21: Field — product
example {α : Type*} [Field α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- Test 22: Field — power
example {α : Type*} [Field α] (a : α) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero

-- Test 23: Rational number constant
example : (7 : ℚ) ≠ 0 := by nonzero

-- Test 24: Negative constant
example : (-5 : ℝ) ≠ 0 := by nonzero

-- Test 25: Product of variable and constant
example (a : ℝ) (ha : a ≠ 0) : 2 * a ≠ 0 := by nonzero

end Tests

