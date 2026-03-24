-- Milestone 4: Negation rule
-- Adds: prove `-a ≠ 0` by recursively proving `a ≠ 0`, then applying neg_ne_zero.mpr

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

/-- Check if `e` has the form `Neg.neg x`, returning `x`. -/
def matchNeg (e : Expr) : Option Expr :=
  match e with
  | Expr.app (Expr.app (Expr.const ``Neg.neg _) _inst) x => some x
  | _ => none

/-- Core recursive procedure: try to prove the current goal `e ≠ 0`.
    `depth` bounds the recursion. -/
partial def proveNonzeroCore (depth : Nat) : TacticM Unit := do
  if depth = 0 then
    throwError "nonzero: recursion depth exceeded"
  let goal ← getMainGoal
  let goalType ← goal.getType
  match matchNe goalType with
  | none => throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"
  | some (_α, e, _z) =>
    -- Step 1: norm_num (literals)
    if ← tryNormNumClose then return
    -- Step 2: assumption
    if ← tryAssumptionClose then return
    -- Step 3: negation rule: if e = -f, prove f ≠ 0 then apply neg_ne_zero.mpr
    if let some f := matchNeg e then
      -- Rewrite goal to `f ≠ 0` and recurse
      evalTactic (← `(tactic| rw [neg_ne_zero]))
      proveNonzeroCore (depth - 1)
      return
    throwTacticEx `nonzero goal "nonzero: unsupported goal"

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do
  proveNonzeroCore 10

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
-- Milestone 3 Tests (preserved)
-- ============================================================

section Milestone3Tests

example (a : ℤ) (ha : a ≠ 0) : a ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : b ≠ 0 := by nonzero
example (α : Type*) [Ring α] (x : α) (hx : x ≠ 0) : x ≠ 0 := by nonzero
example (r : ℝ) (hr : r ≠ 0) : r ≠ 0 := by nonzero
example (q : ℚ) (hq : q ≠ 0) : q ≠ 0 := by nonzero

end Milestone3Tests

-- ============================================================
-- Milestone 4 Tests
-- ============================================================

section Milestone4Tests

-- Simple negation
example (a : ℤ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℚ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- Double negation
example (a : ℤ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero

-- Negation of a literal
example : -(1 : ℤ) ≠ 0 := by nonzero
example : -(2 : ℝ) ≠ 0 := by nonzero

end Milestone4Tests
