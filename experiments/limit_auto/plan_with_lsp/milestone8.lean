import Mathlib

/-!
# limit_auto (Milestone 8) — Guardrails Against Indeterminate Forms

## New Capability
Add a pre-check that refuses dangerous syntactic patterns such as:
- `(t)/(t)` - potential 0/0
- `(t - a)/(t - a)` - potential 0/0 at t = a
- `0/0` - literal indeterminate
- `t/0` - division by zero

## Philosophy
This is intentionally syntactic — perfection is unnecessary.
It is better to fail than to "solve" nonsense.

## Goal
Increase trust in the tactic.
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta Expr

/-- Helper lemma: if `f` is continuous at `a` and `b = f a`, then `Tendsto f (𝓝 a) (𝓝 b)`. -/
theorem tendsto_of_continuousAt_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {a : X} {b : Y} (hcont : ContinuousAt f a) (heq : b = f a) :
    Tendsto f (𝓝 a) (𝓝 b) := by
  rw [heq]
  exact hcont.tendsto

/-- Generalized helper: `-c/x → -∞` as `x → 0⁺` for any `c > 0`. -/
theorem tendsto_neg_const_div_nhdsGT_zero_atBot {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => -c/x) (𝓝[>] 0) atBot := by
  have h : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc
  have h3 : Tendsto (fun x : ℝ => -(c * x)) atTop atBot := tendsto_neg_atTop_atBot.comp h2
  convert h3.comp h using 1
  ext x
  simp only [Function.comp_apply]
  ring

/-- Exponential decay with positive constant: `exp(-c/x) → 0` as `x → 0⁺`. -/
theorem tendsto_exp_neg_const_div_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c/x)) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_const_div_nhdsGT_zero_atBot hc)

/-- Special case: `exp(-1/x) → 0` as `x → 0⁺`. -/
theorem tendsto_exp_neg_one_div_nhdsGT_zero :
    Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_exp_neg_const_div_nhdsGT_zero one_pos

/-!
## Indeterminate Form Detection
-/

/-- Check if an expression is syntactically zero. -/
def isZeroLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 &&
    match e.appFn!.appArg! with
    | .lit (.natVal 0) => true
    | _ => false

/-- Check if two expressions are syntactically equal (simple equality check). -/
def syntacticallyEqual (e1 e2 : Expr) : Bool :=
  e1 == e2

/-- Extract the function body from a lambda, if it's a division. -/
partial def getDivisionParts (e : Expr) : Option (Expr × Expr) :=
  -- Match HDiv.hDiv _ _ _ _ num denom
  if e.isAppOfArity ``HDiv.hDiv 6 then
    some (e.appFn!.appArg!, e.appArg!)
  else
    none

/-- Check if a function body contains a potential indeterminate form.
    Returns `some errorMsg` if problematic, `none` if ok. -/
def checkForIndeterminateForms (fnBody : Expr) : Option String := do
  -- Check for division patterns
  match getDivisionParts fnBody with
  | some (num, denom) =>
    -- Check for t/t pattern (same numerator and denominator)
    if syntacticallyEqual num denom then
      return "potential 0/0 form: numerator equals denominator"
    -- Check for 0/0 literal
    if isZeroLit num && isZeroLit denom then
      return "literal 0/0 detected"
    -- Check for t/0
    if isZeroLit denom then
      return "division by zero detected"
    none
  | none => none

/-- `limit_auto` (Milestone 8): with indeterminate form guardrails. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

  -- Extract the function from Tendsto f F G
  let fn := tgt.appFn!.appFn!.appArg!

  -- If fn is a lambda, check its body for indeterminate forms
  if fn.isLambda then
    let fnBody := fn.bindingBody!
    if let some errMsg := checkForIndeterminateForms fnBody then
      throwError "limit_auto: refusing to handle potential indeterminate form.\n\
        Detected: {errMsg}\n\
        This is a syntactic safety check. If your expression is well-defined, \
        please prove it manually or simplify the expression first."

  -- Normalization pass
  try
    evalTactic (← `(tactic|
      simp only [one_div, add_zero, zero_add, mul_one, one_mul,
                 mul_zero, zero_mul, neg_neg, sub_zero, neg_zero, inv_one]
    ))
  catch _ => pure ()

  -- Try continuity-based rules (Milestone 4)
  try
    evalTactic (← `(tactic|
      first
      | exact ContinuousAt.tendsto (by fun_prop (disch := norm_num))
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by norm_num)
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by simp)
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by ring)
    ))
    return
  catch _ => pure ()

  -- Exponential decay rules (Milestone 7)
  try
    evalTactic (← `(tactic|
      first
      | exact tendsto_exp_neg_one_div_nhdsGT_zero
      | exact tendsto_exp_neg_const_div_nhdsGT_zero (by norm_num)
      | refine tendsto_exp_neg_const_div_nhdsGT_zero ?_; positivity
    ))
    return
  catch _ => pure ()

  -- Reciprocal/Cobounded rules (Milestone 5)
  try
    evalTactic (← `(tactic|
      first
      | exact tendsto_inv₀_nhdsNE_zero
      | exact tendsto_inv_nhdsGT_zero
      | exact tendsto_inv_nhdsLT_zero
      | exact tendsto_inv_atTop_zero
      | exact tendsto_inv_atBot_zero
    ))
    return
  catch _ => pure ()

  throwError "limit_auto: unsupported Tendsto goal.\n\
    Milestone 8 supports:\n\
    • Continuity-based limits: Tendsto f (𝓝 a) (𝓝 (f a))\n\
    • Exponential decay: Tendsto (exp ∘ (-c/·)) (𝓝[>] 0) (𝓝 0) for c > 0\n\
    • Reciprocal limits: Tendsto (·⁻¹) (𝓝[≠] 0) cobounded, etc.\n\
    • Safety: Refuses potential indeterminate forms like t/t, 0/0, t/0"

/-!
## Tests from previous milestones
-/

section PreviousTests

-- Continuity-based (Milestone 4)
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto
example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by limit_auto
example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => x + 0) (𝓝 5) (𝓝 5) := by limit_auto

-- Exponential decay (Milestone 7)
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => Real.exp (-2/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto

-- Reciprocal (Milestone 5)
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℝ) := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := by limit_auto

end PreviousTests

/-!
## Indeterminate form guardrail tests (NEW - Milestone 8)
-/

section IndeterminateFormTests

-- These should be REJECTED by the tactic

/-- error: limit_auto: refusing to handle potential indeterminate form.
Detected: potential 0/0 form: numerator equals denominator
This is a syntactic safety check. If your expression is well-defined, please prove it manually or simplify the expression first. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x / x) (𝓝 1) (𝓝 1) := by limit_auto

/-- error: limit_auto: refusing to handle potential indeterminate form.
Detected: division by zero detected
This is a syntactic safety check. If your expression is well-defined, please prove it manually or simplify the expression first. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x / 0) (𝓝 1) (𝓝 0) := by limit_auto

-- Note: more complex patterns like (x-1)/(x-1) may not be caught by simple syntactic check
-- This is intentional - perfection is not the goal, just basic guardrails

end IndeterminateFormTests

/-!
## Failure tests
-/

section FailureTests

/-- error: limit_auto: goal is not of the form `Tendsto _ _ _` -/
#guard_msgs in
example : True := by limit_auto

end FailureTests

end LimitAuto
