-- Milestone 5: Multiplication rule
-- Adds: prove `a * b ≠ 0` by proving `a ≠ 0` and `b ≠ 0`, then applying mul_ne_zero

import Mathlib.Tactic
import Mathlib.Tactic.NormNum

open Lean Elab Tactic Meta

/-- `nonzero` proves goals of the form `e ≠ 0` using algebraic lemmas. -/
syntax (name := nonzero) "nonzero" : tactic

/-- Check if `e` (after instantiating MVars and whnf) is `lhs ≠ rhs`.
    Returns `(α, lhs, rhs)` with lhs/rhs also instantiated. -/
def matchNe (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e ← instantiateMVars e
  let check : Expr → Option (Expr × Expr × Expr) := fun expr =>
    match expr with
    | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) α) lhs) rhs =>
      some (α, lhs, rhs)
    | Expr.app (Expr.const ``Not _)
        (Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) α) lhs) rhs) =>
      some (α, lhs, rhs)
    | Expr.forallE _ (Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) α) lhs) rhs)
        (Expr.const ``False _) _ =>
      some (α, lhs, rhs)
    | _ => none
  if let some r := check e then return some r
  let e' ← whnf e
  return check e'

/-- Try a tactic on the CURRENT main goal only; restore state if it doesn't close the goal. -/
def tryCloseMainGoal (t : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  let mainGoal ← getMainGoal
  let allGoals ← getGoals
  let otherGoals := allGoals.filter (· != mainGoal)
  setGoals [mainGoal]
  try
    t
    let remaining ← getGoals
    if remaining.isEmpty then
      setGoals otherGoals
      return true
    else
      restoreState s
      return false
  catch _ =>
    restoreState s
    return false

def tryNormNumClose : TacticM Bool := do
  tryCloseMainGoal (evalTactic (← `(tactic| norm_num)))

def tryAssumptionClose : TacticM Bool := do
  tryCloseMainGoal (evalTactic (← `(tactic| assumption)))

/-- Check if `e` (instantiated) has form `Neg.neg x`, returning `x`. -/
def matchNeg (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Neg.neg 3 then return some e.appArg!
  else return none

/-- Check if `e` (instantiated) has form `HMul.hMul f g`, returning `(f, g)`. -/
def matchMul (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``HMul.hMul 6 then
    return some (e.appFn!.appArg!, e.appArg!)
  else return none

/-- Core recursive procedure: try to prove the current main goal `e ≠ 0`.
    `depth` bounds the recursion. -/
partial def proveNonzeroCore (depth : Nat) : TacticM Unit := do
  if depth = 0 then throwError "nonzero: recursion depth exceeded"
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  match ← matchNe goalType with
  | none => throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"
  | some (_α, e, _z) =>
    -- Step 1: norm_num (literals)
    if ← tryNormNumClose then return
    -- Step 2: assumption
    if ← tryAssumptionClose then return
    -- Step 3: negation rule: -f ≠ 0 ← f ≠ 0
    if let some _ ← matchNeg e then
      evalTactic (← `(tactic| rw [neg_ne_zero]))
      proveNonzeroCore (depth - 1)
      return
    -- Step 4: multiplication rule: f * g ≠ 0 ← f ≠ 0, g ≠ 0
    if let some _ ← matchMul e then
      evalTactic (← `(tactic| apply mul_ne_zero))
      proveNonzeroCore (depth - 1)
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
-- Milestone 4 Tests (preserved)
-- ============================================================

section Milestone4Tests

example (a : ℤ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℚ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℤ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero
example : -(1 : ℤ) ≠ 0 := by nonzero
example : -(2 : ℝ) ≠ 0 := by nonzero

end Milestone4Tests

-- ============================================================
-- Milestone 5 Tests
-- ============================================================

section Milestone5Tests

-- Basic products
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero
example (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- Nested products
example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * b * c ≠ 0 := by nonzero

-- Mixed negation and multiplication
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b) ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : (-a) * b ≠ 0 := by nonzero

-- Literal times variable
example (a : ℝ) (ha : a ≠ 0) : 2 * a ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : a * 3 ≠ 0 := by nonzero

end Milestone5Tests
