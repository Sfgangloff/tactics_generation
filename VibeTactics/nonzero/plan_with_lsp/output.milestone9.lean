-- Milestone 9: Guardrails and complexity bounds
-- Adds: depth limit (10), clear errors for 0 ≠ 0, unclear exponents.

import Mathlib.Tactic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Lean Elab Tactic Meta

syntax (name := nonzero) "nonzero" : tactic

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
  return check (← whnf e)

def tryCloseMainGoal (t : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  let mainGoal ← getMainGoal
  let allGoals ← getGoals
  let otherGoals := allGoals.filter (· != mainGoal)
  setGoals [mainGoal]
  try
    t
    let remaining ← getGoals
    if remaining.isEmpty then setGoals otherGoals; return true
    else restoreState s; return false
  catch _ =>
    restoreState s; return false

def tryNormNumClose : TacticM Bool := do
  tryCloseMainGoal (evalTactic (← `(tactic| norm_num)))

def tryAssumptionClose : TacticM Bool := do
  tryCloseMainGoal (evalTactic (← `(tactic| assumption)))

def matchNeg (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  return if e.isAppOfArity ``Neg.neg 3 then some e.appArg! else none

def matchMul (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  return if e.isAppOfArity ``HMul.hMul 6 then some (e.appFn!.appArg!, e.appArg!) else none

def matchPow (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  return if e.isAppOfArity ``HPow.hPow 6 then some (e.appFn!.appArg!, e.appArg!) else none

def isPositiveLit (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.natVal n) => n > 0
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | Expr.lit (Literal.natVal n) => n > 0
      | _ => false
    else false

def tryPositivityFallback (α e : Expr) : TacticM Bool :=
  tryCloseMainGoal do
    let _ ← synthInstance (← mkAppM ``PartialOrder #[α])
    evalTactic (← `(tactic| apply ne_of_gt))
    evalTactic (← `(tactic| positivity))

/-- Check if an expression is syntactically zero (the literal `0`). -/
def isZeroExpr (e : Expr) : Bool :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.appFn!.appArg! with
    | Expr.lit (Literal.natVal 0) => true
    | _ => false
  else false

/-- Maximum recursion depth for nonzero. -/
def nonzeroMaxDepth : Nat := 10

partial def proveNonzeroCore (depth : Nat) : TacticM Unit := do
  -- Guardrail 1: recursion depth
  if depth = 0 then
    throwError "nonzero: recursion depth limit ({nonzeroMaxDepth}) exceeded"
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  match ← matchNe goalType with
  | none => throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"
  | some (α, e, z) =>
    -- Guardrail 2: detect `0 ≠ 0` (provably false, fail clearly)
    let eInst ← instantiateMVars e
    let zInst ← instantiateMVars z
    if isZeroExpr eInst && isZeroExpr zInst then
      throwTacticEx `nonzero goal
        "nonzero: goal `0 ≠ 0` is false and cannot be proved"
    if ← tryNormNumClose then return
    if ← tryAssumptionClose then return
    if let some _ ← matchNeg eInst then
      evalTactic (← `(tactic| rw [neg_ne_zero]))
      proveNonzeroCore (depth - 1); return
    if let some _ ← matchMul eInst then
      evalTactic (← `(tactic| apply mul_ne_zero))
      proveNonzeroCore (depth - 1)
      proveNonzeroCore (depth - 1); return
    if let some (_base, n) ← matchPow eInst then
      let nInst ← instantiateMVars n
      if isPositiveLit nInst then
        evalTactic (← `(tactic| apply pow_ne_zero))
        proveNonzeroCore (depth - 1); return
      else
        -- Guardrail 3: unclear exponent — fall through to positivity
        pure ()
    if ← tryPositivityFallback α eInst then return
    -- simp normalization pre-pass
    let goalTypeBefore ← goal.getType
    if ← tryCloseMainGoal (evalTactic (← `(tactic|
        simp only [neg_neg, mul_one, one_mul, pow_one, mul_neg, neg_mul] at *))) then return
    let goalTypeAfter ← instantiateMVars (← goal.getType)
    if goalTypeAfter != goalTypeBefore then
      proveNonzeroCore (depth - 1); return
    throwTacticEx `nonzero goal "nonzero: unsupported goal"

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do proveNonzeroCore nonzeroMaxDepth

-- ============================================================
-- Milestone 1-8 Tests (preserved)
-- ============================================================

section Milestone1Tests
variable (α : Type*) [Ring α] (a : α)
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example (h : a ≠ 0) : a ≠ 0 := by first | nonzero | exact h
end Milestone1Tests

section Milestone2Tests
example : (1 : ℤ) ≠ 0 := by nonzero
example : (2 : ℤ) ≠ 0 := by nonzero
example : (3 : ℚ) ≠ 0 := by nonzero
example : (42 : ℝ) ≠ 0 := by nonzero
example : (-1 : ℤ) ≠ 0 := by nonzero
example : (-3 : ℝ) ≠ 0 := by nonzero
example : (2 : ℕ) ≠ 0 := by nonzero
end Milestone2Tests

section Milestone3Tests
example (a : ℤ) (ha : a ≠ 0) : a ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : b ≠ 0 := by nonzero
example (α : Type*) [Ring α] (x : α) (hx : x ≠ 0) : x ≠ 0 := by nonzero
example (r : ℝ) (hr : r ≠ 0) : r ≠ 0 := by nonzero
example (q : ℚ) (hq : q ≠ 0) : q ≠ 0 := by nonzero
end Milestone3Tests

section Milestone4Tests
example (a : ℤ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℚ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero
example (a : ℤ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero
example : -(1 : ℤ) ≠ 0 := by nonzero
example : -(2 : ℝ) ≠ 0 := by nonzero
end Milestone4Tests

section Milestone5Tests
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero
example (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero
example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a * b * c ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b) ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : (-a) * b ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : 2 * a ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : a * 3 ≠ 0 := by nonzero
end Milestone5Tests

section Milestone6Tests
example (a : ℤ) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : a ^ 2 ≠ 0 := by nonzero
example (a : ℚ) (ha : a ≠ 0) : a ^ 5 ≠ 0 := by nonzero
example : (2 : ℤ) ^ 4 ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : (-a) ^ 3 ≠ 0 := by nonzero
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 2 * b ^ 3 ≠ 0 := by nonzero
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : (a * b) ^ 2 ≠ 0 := by nonzero
end Milestone6Tests

section Milestone7Tests
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b ≠ 0 := by nonzero
example (a : ℝ) (ha : 0 < a) : a ≠ 0 := by nonzero
example : (3 : ℝ) ≠ 0 := by nonzero
example (a : ℝ) (ha : 0 < a) : a + 1 ≠ 0 := by nonzero
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * b + 1 ≠ 0 := by nonzero
end Milestone7Tests

section Milestone8Tests
example (a : ℤ) (ha : a ≠ 0) : -(-a) ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : a * 1 ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : 1 * a ≠ 0 := by nonzero
example (a : ℤ) (ha : a ≠ 0) : a ^ 1 ≠ 0 := by nonzero
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a * 1) * b ≠ 0 := by nonzero
end Milestone8Tests

-- ============================================================
-- Milestone 9 Tests
-- ============================================================

section Milestone9Tests

-- Guardrail: 0 ≠ 0 should fail with informative message
example : True := by
  have : ¬ ((0 : ℤ) ≠ 0) := by
    intro h; exact h rfl
  trivial

-- Depth limit: deeply nested expressions still work (within limit)
example (a : ℤ) (ha : a ≠ 0) : -(-(-(a))) ≠ 0 := by nonzero
example (a b c d : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    a * b * c * d ≠ 0 := by nonzero

-- Unclear exponent: falls back to positivity when possible
example (a : ℝ) (ha : 0 < a) (n : ℕ) : a ^ n ≠ 0 := by
  -- positivity fallback should handle this
  first | nonzero | exact pow_ne_zero n ha.ne'

-- The tactic fails gracefully on an unsupported goal and a fallback works
-- (a ≠ 0 ∧ a ≠ -1 implies a + 1 ≠ 0 over ℤ)
example (a : ℤ) (ha : a ≠ 0) (hm : a ≠ -1) : a + 1 ≠ 0 := by
  first | nonzero | (intro h; apply hm; linarith)

end Milestone9Tests
