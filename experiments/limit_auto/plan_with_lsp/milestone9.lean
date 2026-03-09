import Mathlib

/-!
# limit_auto (Milestone 9) — Internal Refactor for Long-Term Stability

## New Capability
No new mathematical power — only structural improvement.

## Decomposition
- `normalize`: Expr → TacticM Expr
- `classify`: (f, F, G) → Option Rule
- `applyRule`: Rule → TacticM Unit

## Tracing
Add trace option `trace.limit_auto` printing:
- detected rule
- matched subexpressions
- lemma used

This makes future extensions safe.
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta Expr

/-!
## Helper Lemmas (from previous milestones)
-/

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

/-- Exponential decay with positive constant. -/
theorem tendsto_exp_neg_const_div_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c/x)) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_const_div_nhdsGT_zero_atBot hc)

/-- Special case: `exp(-1/x) → 0` as `x → 0⁺`. -/
theorem tendsto_exp_neg_one_div_nhdsGT_zero :
    Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_exp_neg_const_div_nhdsGT_zero one_pos

/-!
## Rule Classification
-/

/-- The rules that limit_auto can apply. -/
inductive LimitRule where
  | continuity          -- ContinuousAt-based
  | exponentialDecay    -- exp(-c/x) patterns
  | reciprocal          -- x⁻¹ and cobounded patterns
  | unsupported
  deriving Repr, BEq

instance : ToString LimitRule where
  toString
    | .continuity => "continuity"
    | .exponentialDecay => "exponential_decay"
    | .reciprocal => "reciprocal"
    | .unsupported => "unsupported"

/-!
## Indeterminate Form Detection (from Milestone 8)
-/

/-- Check if an expression is syntactically zero. -/
def isZeroLit (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 &&
    match e.appFn!.appArg! with
    | .lit (.natVal 0) => true
    | _ => false

/-- Extract division parts if present. -/
def getDivisionParts (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HDiv.hDiv 6 then
    some (e.appFn!.appArg!, e.appArg!)
  else
    none

/-- Check for indeterminate forms. Returns error message if problematic. -/
def checkForIndeterminateForms (fnBody : Expr) : Option String := do
  match getDivisionParts fnBody with
  | some (num, denom) =>
    if num == denom then
      return "potential 0/0 form: numerator equals denominator"
    if isZeroLit num && isZeroLit denom then
      return "literal 0/0 detected"
    if isZeroLit denom then
      return "division by zero detected"
    none
  | none => none

/-!
## Tracing Infrastructure
-/

initialize registerTraceClass `limit_auto

/-- Log a trace message for limit_auto. -/
def traceLimit (msg : String) : TacticM Unit := do
  trace[limit_auto] "{msg}"

/-!
## Core Tactic Components
-/

/-- Normalize the goal expression with conservative rewrites. -/
def normalizeGoal : TacticM Unit := do
  traceLimit "normalizing goal..."
  try
    evalTactic (← `(tactic|
      simp only [one_div, add_zero, zero_add, mul_one, one_mul,
                 mul_zero, zero_mul, neg_neg, sub_zero, neg_zero, inv_one]
    ))
    traceLimit "normalization applied"
  catch _ =>
    traceLimit "normalization had no effect"

/-- Classify the goal to determine which rule to apply. -/
def classifyGoal (tgt : Expr) : TacticM LimitRule := do
  -- For now, we'll try rules in order and see which succeeds
  -- A more sophisticated classifier could inspect the expression structure
  traceLimit "classifying goal..."

  -- Extract f, F, G from Tendsto f F G
  let f := tgt.appFn!.appFn!.appArg!

  -- Check if it looks like exponential decay
  if f.isLambda then
    let body := f.bindingBody!
    if body.isAppOf ``Real.exp then
      traceLimit "detected: exponential pattern"
      return .exponentialDecay

  -- Check if it looks like reciprocal
  if f.isLambda then
    let body := f.bindingBody!
    if body.isAppOf ``Inv.inv then
      traceLimit "detected: reciprocal pattern"
      return .reciprocal

  -- Default to trying continuity
  traceLimit "defaulting to: continuity rule"
  return .continuity

/-- Apply the continuity rule. -/
def applyContinuityRule : TacticM Unit := do
  traceLimit "applying continuity rule..."
  evalTactic (← `(tactic|
    first
    | exact ContinuousAt.tendsto (by fun_prop (disch := norm_num))
    | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by norm_num)
    | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by simp)
    | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by ring)
  ))
  traceLimit "continuity rule succeeded"

/-- Apply the exponential decay rule. -/
def applyExponentialDecayRule : TacticM Unit := do
  traceLimit "applying exponential decay rule..."
  evalTactic (← `(tactic|
    first
    | exact tendsto_exp_neg_one_div_nhdsGT_zero
    | exact tendsto_exp_neg_const_div_nhdsGT_zero (by norm_num)
    | refine tendsto_exp_neg_const_div_nhdsGT_zero ?_; positivity
  ))
  traceLimit "exponential decay rule succeeded"

/-- Apply the reciprocal rule. -/
def applyReciprocalRule : TacticM Unit := do
  traceLimit "applying reciprocal rule..."
  evalTactic (← `(tactic|
    first
    | exact tendsto_inv₀_nhdsNE_zero
    | exact tendsto_inv_nhdsGT_zero
    | exact tendsto_inv_nhdsLT_zero
    | exact tendsto_inv_atTop_zero
    | exact tendsto_inv_atBot_zero
  ))
  traceLimit "reciprocal rule succeeded"

/-- Apply a specific rule. -/
def applyRule (rule : LimitRule) : TacticM Unit := do
  match rule with
  | .continuity => applyContinuityRule
  | .exponentialDecay => applyExponentialDecayRule
  | .reciprocal => applyReciprocalRule
  | .unsupported => throwError "limit_auto: no applicable rule"

/-!
## Main Tactic
-/

/-- `limit_auto` (Milestone 9): with clean architecture and tracing. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  traceLimit "goal: {tgt}"

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

  -- Extract the function and check for indeterminate forms
  let fn := tgt.appFn!.appFn!.appArg!
  if fn.isLambda then
    let fnBody := fn.bindingBody!
    if let some errMsg := checkForIndeterminateForms fnBody then
      throwError "limit_auto: refusing to handle potential indeterminate form.\n\
        Detected: {errMsg}\n\
        This is a syntactic safety check. If your expression is well-defined, \
        please prove it manually or simplify the expression first."

  -- Step 1: Normalize
  normalizeGoal

  -- Step 2: Classify
  let rule ← classifyGoal tgt

  -- Step 3: Try the classified rule first, then fall back to others
  try
    applyRule rule
    return
  catch _ => pure ()

  -- Fallback: try all rules in order
  traceLimit "classified rule failed, trying all rules..."

  for r in [LimitRule.continuity, .exponentialDecay, .reciprocal] do
    if r != rule then
      try
        applyRule r
        return
      catch _ => pure ()

  throwError "limit_auto: unsupported Tendsto goal.\n\
    Milestone 9 supports:\n\
    • Continuity-based limits: Tendsto f (𝓝 a) (𝓝 (f a))\n\
    • Exponential decay: Tendsto (exp ∘ (-c/·)) (𝓝[>] 0) (𝓝 0) for c > 0\n\
    • Reciprocal limits: Tendsto (·⁻¹) (𝓝[≠] 0) cobounded, etc.\n\
    • Safety: Refuses potential indeterminate forms\n\
    Use `set_option trace.limit_auto true` for debugging."

/-!
## Tests from previous milestones
-/

section PreviousTests

-- Continuity-based
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto
example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by limit_auto
example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => x + 0) (𝓝 5) (𝓝 5) := by limit_auto

-- Exponential decay
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => Real.exp (-2/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto

-- Reciprocal
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℝ) := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := by limit_auto

end PreviousTests

/-!
## Tracing demonstration (uncomment to see output)
-/

-- set_option trace.limit_auto true in
-- example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto

/-!
## Indeterminate form tests
-/

section IndeterminateFormTests

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
