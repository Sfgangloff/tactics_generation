-- Milestone 2: Nonzero numeric literals
-- Adds: dispatch to norm_num for numeric literal goals like (2 : ℤ) ≠ 0

import Mathlib.Tactic
import Mathlib.Tactic.NormNum

open Lean Elab Tactic Meta

/-- `nonzero` proves goals of the form `e ≠ 0` using algebraic lemmas. -/
syntax (name := nonzero) "nonzero" : tactic

/-- Check if an expression is `Ne e z` (i.e., `e ≠ z`), returning `(α, e, z)`. -/
def matchNe (e : Expr) : Option (Expr × Expr × Expr) :=
  match e with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) α) lhs) rhs =>
    some (α, lhs, rhs)
  | _ => none

/-- Try norm_num; return true if it closes all goals. -/
def tryNormNumClose : TacticM Bool := do
  try
    evalTactic (← `(tactic| norm_num))
    let goals ← getGoals
    return goals.isEmpty
  catch _ =>
    return false

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match matchNe goalType with
  | some (_α, _e, _z) =>
    -- Try norm_num (handles numeric literals like 1 ≠ 0, 2 ≠ 0, -3 ≠ 0)
    if ← tryNormNumClose then return
    -- More rules will be added in later milestones
    throwTacticEx `nonzero goal "nonzero: unsupported goal"
  | none =>
    throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"

-- ============================================================
-- Milestone 1 Tests (preserved)
-- ============================================================

section Milestone1Tests

variable (α : Type*) [Ring α] (a : α)

-- nonzero fails on non-literal; `first` falls back to exact h
example (h : a ≠ 0) : a ≠ 0 := by
  first | nonzero | exact h

end Milestone1Tests

-- ============================================================
-- Milestone 2 Tests
-- ============================================================

section Milestone2Tests

-- Positive integer literals
example : (1 : ℤ) ≠ 0 := by nonzero
example : (2 : ℤ) ≠ 0 := by nonzero
example : (3 : ℚ) ≠ 0 := by nonzero
example : (42 : ℝ) ≠ 0 := by nonzero

-- Negative literals
example : (-1 : ℤ) ≠ 0 := by nonzero
example : (-3 : ℝ) ≠ 0 := by nonzero

-- Natural number literals
example : (2 : ℕ) ≠ 0 := by nonzero

end Milestone2Tests
