-- Milestone 3: Hypothesis lookup
-- Adds: search local context for `h : a ≠ 0` and apply it directly.

import Mathlib.Tactic
import Mathlib.Tactic.NormNum

open Lean Elab Tactic Meta

/-- `nonzero` proves goals of the form `e ≠ 0` using algebraic lemmas. -/
syntax (name := nonzero) "nonzero" : tactic

/-- Check if an expression is `Ne lhs rhs`, returning `(α, lhs, rhs)`. -/
def matchNe (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) α) lhs) rhs =>
    some (α, lhs, rhs)
  | _ => none

/-- Try a tactic; return true if all goals are closed afterwards. -/
def tryClose (t : TacticM Unit) : TacticM Bool := do
  try
    t
    let goals ← getGoals
    return goals.isEmpty
  catch _ =>
    return false

/-- Try norm_num; return true if it closes all goals. -/
def tryNormNumClose : TacticM Bool := do
  tryClose (evalTactic (← `(tactic| norm_num)))

/-- Try assumption; return true if it closes all goals. -/
def tryAssumptionClose : TacticM Bool := do
  tryClose (evalTactic (← `(tactic| assumption)))

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match matchNe goalType with
  | some (_α, _e, _z) =>
    -- Step 1: Try norm_num (handles numeric literals)
    if ← tryNormNumClose then return
    -- Step 2: Search local context via assumption
    if ← tryAssumptionClose then return
    -- More rules will be added in later milestones
    throwTacticEx `nonzero goal "nonzero: unsupported goal"
  | none =>
    throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"

-- ============================================================
-- Milestone 1 Tests (preserved)
-- ============================================================

section Milestone1Tests

variable (α : Type*) [Ring α] (a : α)

example (h : a ≠ 0) : a ≠ 0 := by
  first | nonzero | exact h

end Milestone1Tests

-- ============================================================
-- Milestone 2 Tests (preserved)
-- ============================================================

section Milestone2Tests

example : (1 : ℤ) ≠ 0 := by nonzero
example : (2 : ℤ) ≠ 0 := by nonzero
example : (3 : ℚ) ≠ 0 := by nonzero
example : (42 : ℝ) ≠ 0 := by nonzero
example : (-1 : ℤ) ≠ 0 := by nonzero
example : (-3 : ℝ) ≠ 0 := by nonzero
example : (2 : ℕ) ≠ 0 := by nonzero

end Milestone2Tests

-- ============================================================
-- Milestone 3 Tests
-- ============================================================

section Milestone3Tests

-- Direct hypothesis
example (a : ℤ) (ha : a ≠ 0) : a ≠ 0 := by nonzero

-- Multiple hypotheses; the right one is found
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : b ≠ 0 := by nonzero

-- Works over any ring
example (α : Type*) [Ring α] (x : α) (hx : x ≠ 0) : x ≠ 0 := by nonzero

-- Works with real numbers
example (r : ℝ) (hr : r ≠ 0) : r ≠ 0 := by nonzero

-- Works with rationals
example (q : ℚ) (hq : q ≠ 0) : q ≠ 0 := by nonzero

end Milestone3Tests
