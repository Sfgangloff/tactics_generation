-- Milestone 6: Power rule
-- Adds: prove `a ^ n ≠ 0` by proving `a ≠ 0`, applying pow_ne_zero

import Mathlib.Tactic
import Mathlib.Tactic.NormNum

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
  return if e.isAppOfArity ``HMul.hMul 6
    then some (e.appFn!.appArg!, e.appArg!)
    else none

/-- Check if `e` has the form `HPow.hPow base n`, returning `(base, n)`.
    `@HPow.hPow α β γ inst base n` has arity 6. -/
def matchPow (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  return if e.isAppOfArity ``HPow.hPow 6
    then some (e.appFn!.appArg!, e.appArg!)
    else none

/-- Check whether a natural-number literal expression is > 0.
    Handles both raw `Expr.lit (natVal n)` and `@OfNat.ofNat ℕ n inst`. -/
def isPositiveLit (e : Expr) : Bool :=
  match e with
  | Expr.lit (Literal.natVal n) => n > 0
  | _ =>
    -- @OfNat.ofNat α n inst  has arity 3; the literal is the SECOND arg: appFn!.appArg!
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | Expr.lit (Literal.natVal n) => n > 0
      | _ => false
    else false

partial def proveNonzeroCore (depth : Nat) : TacticM Unit := do
  if depth = 0 then throwError "nonzero: recursion depth exceeded"
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  match ← matchNe goalType with
  | none => throwTacticEx `nonzero goal "nonzero: goal is not of the form `e ≠ 0`"
  | some (_α, e, _z) =>
    if ← tryNormNumClose then return
    if ← tryAssumptionClose then return
    -- Negation rule
    if let some _ ← matchNeg e then
      evalTactic (← `(tactic| rw [neg_ne_zero]))
      proveNonzeroCore (depth - 1); return
    -- Multiplication rule
    if let some _ ← matchMul e then
      evalTactic (← `(tactic| apply mul_ne_zero))
      proveNonzeroCore (depth - 1)
      proveNonzeroCore (depth - 1); return
    -- Power rule: a ^ n ≠ 0 ← a ≠ 0 (when n is a positive literal)
    if let some (base, n) ← matchPow e then
      let nInst ← instantiateMVars n
      if isPositiveLit nInst then
        -- pow_ne_zero : ∀ n, a ≠ 0 → a ^ n ≠ 0
        evalTactic (← `(tactic| apply pow_ne_zero))
        proveNonzeroCore (depth - 1); return
    let fn := e.getAppFn; let args := e.getAppArgs
    logInfo m!"[nonzero] unsupported: e={e}, head={fn.constName?}, nargs={args.size}, isAppOfArity HPow 6={e.isAppOfArity ``HPow.hPow 6}"
    throwTacticEx `nonzero goal "nonzero: unsupported goal"

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do proveNonzeroCore 10

-- ============================================================
-- Milestone 1-5 Tests (preserved)
-- ============================================================

section Milestone1Tests
variable (α : Type*) [Ring α] (a : α)
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

-- ============================================================
-- Milestone 6 Tests
-- ============================================================

section Milestone6Tests

-- Basic powers
example (a : ℤ) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero
example (a : ℝ) (ha : a ≠ 0) : a ^ 2 ≠ 0 := by nonzero
example (a : ℚ) (ha : a ≠ 0) : a ^ 5 ≠ 0 := by nonzero

-- Power of a literal
example : (2 : ℤ) ^ 4 ≠ 0 := by nonzero

-- Negative base to a power
example (a : ℝ) (ha : a ≠ 0) : (-a) ^ 3 ≠ 0 := by nonzero

-- Product of powers
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : a ^ 2 * b ^ 3 ≠ 0 := by nonzero

-- Power of a product
example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : (a * b) ^ 2 ≠ 0 := by nonzero

end Milestone6Tests
