import Mathlib

open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta
open Filter Topology Real Bornology

/-!
# `limit_auto`

A tactic that automatically proves limit goals of the form `Tendsto f F G` by
syntactic pattern-matching on `f` and selecting the appropriate Mathlib theorem.

## Supported pattern classes (from the spec)

- **Class 1 — Continuity**: `f` is a composition of known continuous functions.
  Proof method: `Continuous.tendsto'` with `fun_prop`/`continuity` and `simp`.
  Filter pair: `(𝓝 a, 𝓝 (f a))`.

- **Class 2 — Exponential decay**: body of `f` mentions `Real.exp` or `Complex.exp`.
  Key lemmas: `Real.tendsto_exp_neg_atTop_nhds_zero`, `Real.tendsto_exp_atBot`.
  Filter pairs: `(atTop, 𝓝 0)`, `(atBot, 𝓝 0)`, `(atBot, 𝓝[>] 0)`.

- **Class 3 — Reciprocal**: body of `f` is `Inv.inv` applied to the bound variable,
  or `1 / (bound variable)`.
  Key lemmas: `Filter.tendsto_inv₀_nhdsWithin_ne_zero`, `Filter.tendsto_inv₀_cobounded'`.
  Filter pairs: `(𝓝[≠] 0, cobounded)` or `(cobounded, 𝓝[≠] 0)`.

## Safety

Detects and rejects syntactically indeterminate forms:
- `t / t`   — numerator and denominator are syntactically equal
- `t / 0`   — denominator is the literal `0`
- `0 / 0`   — both
- `(t-a)/(t-a)` — covered by the `num == den` check

## Algorithm

1. **Goal Analysis**: extract `(f, F, G)` from `Tendsto f F G`.
2. **Safety check**: refuse indeterminate forms in `f`.
3. **Pattern Classification**: classify `f` into Class 1, 2, or 3.
4. **Proof Construction**: apply the primary rule; fall back to the other classes.
5. **Fallback**: fail with an informative error message.
-/

namespace LimitAuto

/-! ## Goal parsing -/

/-- Extract `(f, F, G)` from a `Tendsto f F G` expression.
    `Filter.Tendsto` takes two implicit universe-polymorphic type arguments and then
    three explicit arguments, so the fully-applied `Expr` has arity 5:
    `@Filter.Tendsto α β f F G`. -/
def matchTendsto? (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity `Filter.Tendsto 5 then
    let a := e.getAppArgs
    some (a[2]!, a[3]!, a[4]!)
  else
    none

/-! ## Indeterminate-form detection -/

/-- Return `true` if `e` syntactically contains a division `num / den` where
    - `den` is the literal `0`, or
    - `num` and `den` are syntactically identical (covers `t/t`, `(t-a)/(t-a)`). -/
partial def containsIndeterminate : Expr → Bool
  | .lam _ _ b _    => containsIndeterminate b
  | .letE _ _ v b _ => containsIndeterminate v || containsIndeterminate b
  | e =>
    -- HDiv.hDiv has four implicit args (α β γ inst) then two explicit (a b), arity = 6
    if e.isAppOfArity `HDiv.hDiv 6 then
      let args := e.getAppArgs
      let num  := args[4]!
      let den  := args[5]!
      -- den is the literal 0?
      let denIsZero :=
        den.isAppOfArity `OfNat.ofNat 3 &&
        (den.getAppArgs[1]! == .lit (.natVal 0))
      if denIsZero || num == den then true
      else args.any containsIndeterminate
    else
      e.getAppArgs.any containsIndeterminate

/-! ## Pattern classification -/

/-- Recursively check whether `e` mentions `Real.exp` or `Complex.exp`. -/
private partial def mentionsExp : Expr → Bool
  | e =>
    if e.isAppOf `Real.exp || e.isAppOf `Complex.exp then true
    else e.getAppArgs.any mentionsExp

/-- Check whether `body` (the body of a single-argument lambda) is of the form
    `x⁻¹` or `1 / x`, where `x` is the bound variable at de Bruijn index 0. -/
private def isInvOfBVar (body : Expr) : Bool :=
  -- x⁻¹  →  @Inv.inv α inst (.bvar 0)  (arity 3: type, instance, value)
  if body.isAppOfArity `Inv.inv 3 then
    body.getAppArgs[2]!.isBVar
  -- 1 / x  →  @HDiv.hDiv α β γ inst 1 (.bvar 0)  (arity 6)
  else if body.isAppOfArity `HDiv.hDiv 6 then
    let args := body.getAppArgs
    let num  := args[4]!
    let den  := args[5]!
    den.isBVar &&
      num.isAppOfArity `OfNat.ofNat 3 &&
      (num.getAppArgs[1]! == .lit (.natVal 1))
  else
    false

/-- The three pattern classes from the spec. -/
inductive PatternClass where
  | Continuity
  | ExponentialDecay
  | Reciprocal

/-- Classify `f` by shallow syntactic inspection of its lambda body.
    Priority: Reciprocal > ExponentialDecay > Continuity (tried speculatively). -/
def classifyFunction : Expr → PatternClass
  | .lam _ _ body _ =>
    if isInvOfBVar body then .Reciprocal
    else if mentionsExp body then .ExponentialDecay
    else .Continuity
  | _ => .Continuity

/-! ## Helper: run a tactic, returning Bool -/

/-- Try `tac`; return `true` iff it closes the current goal without error. -/
private def tryTac (tac : Syntax) : TacticM Bool :=
  try evalTactic tac; pure true catch _ => pure false

/-! ## Class 1 — Continuity

Spec proof method: `Continuous.tendsto' (by continuity) _ _ (by simp)`.

`Continuous.tendsto' : Continuous f → ∀ x y, f x = y → Tendsto f (𝓝 x) (𝓝 y)` -/

def applyContinuity : TacticM Bool := do
  -- Primary: apply Continuous.tendsto' and close remaining subgoals
  if ← tryTac (← `(tactic|
      apply Continuous.tendsto' <;>
        first | fun_prop | continuity | norm_num | ring | rfl | simp))
    then return true
  -- ContinuousAt.tendsto when the goal already has the form Tendsto f (𝓝 a) (𝓝 (f a))
  if ← tryTac (← `(tactic| exact ContinuousAt.tendsto (by fun_prop))) then return true
  if ← tryTac (← `(tactic| exact ContinuousAt.tendsto (by continuity))) then return true
  if ← tryTac (← `(tactic| apply ContinuousAt.tendsto; fun_prop)) then return true
  if ← tryTac (← `(tactic| apply ContinuousAt.tendsto; continuity)) then return true
  -- Spec-mandated explicit form with rfl for the value equality
  if ← tryTac (← `(tactic| exact Continuous.tendsto' (by fun_prop) _ _ rfl)) then return true
  if ← tryTac (← `(tactic| exact Continuous.tendsto' (by continuity) _ _ rfl)) then return true
  return false

/-! ## Class 2 — Exponential decay

Key Mathlib lemmas:
- `Real.tendsto_exp_neg_atTop_nhds_zero` : `Tendsto (fun x => exp (-x)) atTop (𝓝 0)`
- `Real.tendsto_exp_atBot`               : `Tendsto Real.exp atBot (𝓝 0)`
- `Real.tendsto_exp_atBot_nhdsGT`        : `Tendsto Real.exp atBot (𝓝[>] 0)` -/

def applyExponentialDecay : TacticM Bool := do
  -- exp(-x) → 0 at +∞  (canonical form)
  if ← tryTac (← `(tactic| exact Real.tendsto_exp_neg_atTop_nhds_zero)) then return true
  -- exp(x) → 0 at -∞
  if ← tryTac (← `(tactic| exact Real.tendsto_exp_atBot)) then return true
  -- exp(x) → 𝓝[>] 0 at -∞
  if ← tryTac (← `(tactic| exact Real.tendsto_exp_atBot_nhdsGT)) then return true
  -- Alternative name spellings (Mathlib naming conventions vary)
  if ← tryTac (← `(tactic| exact Real.tendsto_exp_neg_atTop_nhds_0)) then return true
  if ← tryTac (← `(tactic| exact tendsto_exp_neg_atTop_nhds_zero)) then return true
  -- Composition approach: rewrite goal to `tendsto_exp_comp_nhds_zero`
  if ← tryTac (← `(tactic|
      rw [Real.tendsto_exp_comp_nhds_zero]; exact tendsto_neg_atTop_atBot))
    then return true
  if ← tryTac (← `(tactic|
      rw [Real.tendsto_exp_comp_nhds_zero]
      simp [tendsto_neg_atTop_atBot]))
    then return true
  return false

/-! ## Class 3 — Reciprocal

Key Mathlib lemmas (in a `NormedDivisionRing`):
- `Filter.tendsto_inv₀_nhdsWithin_ne_zero` : `Tendsto Inv.inv (𝓝[≠] 0) (cobounded α)`
- `Filter.tendsto_inv₀_cobounded'`         : `Tendsto Inv.inv (cobounded α) (𝓝[≠] 0)` -/

def applyReciprocal : TacticM Bool := do
  -- Try the most probable Mathlib 4 names (cannot verify without LSP)
  if ← tryTac (← `(tactic| exact Filter.tendsto_inv₀_nhdsWithin_ne_zero)) then return true
  if ← tryTac (← `(tactic| exact Filter.tendsto_inv₀_cobounded'))         then return true
  if ← tryTac (← `(tactic| exact Filter.tendsto_inv₀_nhdsNE_zero))        then return true
  -- Without namespace qualifier
  if ← tryTac (← `(tactic| exact tendsto_inv₀_nhdsWithin_ne_zero))        then return true
  if ← tryTac (← `(tactic| exact tendsto_inv₀_cobounded'))                then return true
  if ← tryTac (← `(tactic| exact tendsto_inv₀_nhdsNE_zero))               then return true
  -- Older / alternative spellings
  if ← tryTac (← `(tactic| exact tendsto_inv_nhdsWithin_ne_zero))         then return true
  if ← tryTac (← `(tactic| exact tendsto_inv_cobounded))                  then return true
  return false

end LimitAuto

/-! ## The `limit_auto` tactic -/

initialize Lean.registerTraceClass `limit_auto

/-- `limit_auto` proves limit goals `Tendsto f F G` by syntactic pattern matching.

    **Supported patterns**:

    - *Continuity* (Class 1): proved via `Continuous.tendsto'` + `fun_prop`/`continuity`.
    - *Exponential decay* (Class 2): uses `Real.tendsto_exp_neg_atTop_nhds_zero` etc.
    - *Reciprocal* (Class 3): uses `Filter.tendsto_inv₀_nhdsWithin_ne_zero` etc.

    **Safety**: refuses syntactically indeterminate forms (`t/t`, `(t-a)/(t-a)`,
    `t/0`, `0/0`).
-/
syntax (name := limitAuto) "limit_auto" : tactic

@[tactic limitAuto]
def evalLimitAuto : Tactic := fun _ => do
  let goal ← getMainGoal
  let ty   ← goal.getType
  let ty   ← instantiateMVars ty

  -- Step 1: Goal Analysis — must be `Tendsto f F G`
  let some (f, _F, _G) := LimitAuto.matchTendsto? ty
    | throwTacticEx `limit_auto goal
        m!"limit_auto: goal is not of the form 'Tendsto f F G'"

  -- Step 2: Safety — refuse indeterminate forms
  if LimitAuto.containsIndeterminate f then
    throwTacticEx `limit_auto goal
      m!"limit_auto: refusing to solve goal with indeterminate form (t/t, t/0, 0/0, …)"

  -- Step 3: Pattern Classification
  let cls := LimitAuto.classifyFunction f
  let clsName : String := match cls with
    | .Reciprocal       => "Reciprocal"
    | .ExponentialDecay => "ExponentialDecay"
    | .Continuity       => "Continuity"
  trace[limit_auto] "limit_auto: classified as {clsName}"

  -- Step 4: Proof Construction — primary class first, then ordered fallbacks
  let solved ← match cls with
    | .Reciprocal => do
        if ← LimitAuto.applyReciprocal   then pure true
        else LimitAuto.applyContinuity
    | .ExponentialDecay => do
        if ← LimitAuto.applyExponentialDecay then pure true
        else LimitAuto.applyContinuity
    | .Continuity => do
        if ← LimitAuto.applyContinuity        then pure true
        else if ← LimitAuto.applyReciprocal   then pure true
        else LimitAuto.applyExponentialDecay

  -- Step 5: Fallback — informative error
  if !solved then
    throwTacticEx `limit_auto goal
      m!"limit_auto: no matching rule found for this Tendsto goal"

/-! ## Tests -/

section Tests

-- ── Class 1: Continuity ────────────────────────────────────────────────────

-- Spec easy example
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto

-- Identity
example : Tendsto (fun x : ℝ => x) (𝓝 5) (𝓝 5) := by limit_auto

-- Scaling
example : Tendsto (fun x : ℝ => 2 * x) (𝓝 3) (𝓝 6) := by limit_auto

-- Constant function
example : Tendsto (fun _ : ℝ => (42 : ℝ)) (𝓝 0) (𝓝 42) := by limit_auto

-- Quadratic (spec medium example)
example : Tendsto (fun x : ℝ => x ^ 2) (𝓝 3) (𝓝 9) := by limit_auto

-- Exponential is continuous (limit at a finite point)
example : Tendsto Real.exp (𝓝 0) (𝓝 1) := by limit_auto

-- Spec medium: sin(x² + 1) at 0
example : Tendsto (fun x : ℝ => Real.sin (x ^ 2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  limit_auto

-- Spec hard: nested composition exp ∘ sin ∘ cos at π
example : Tendsto (fun x : ℝ => Real.exp (Real.sin (Real.cos x)))
    (𝓝 Real.pi) (𝓝 (Real.exp (Real.sin (Real.cos Real.pi)))) := by
  limit_auto

-- ── Class 2: Exponential decay ────────────────────────────────────────────

-- exp(-x) → 0 as x → +∞
example : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by limit_auto

-- exp(x) → 0 as x → -∞
example : Tendsto Real.exp atBot (𝓝 0) := by limit_auto

-- ── Class 3: Reciprocal ───────────────────────────────────────────────────

-- Spec easy: x⁻¹ from 𝓝[≠] 0 goes to cobounded
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded ℝ) := by limit_auto

-- Spec easy: x⁻¹ from cobounded goes back to 𝓝[≠] 0
example : Tendsto (fun x : ℝ => x⁻¹) (cobounded ℝ) (𝓝[≠] 0) := by limit_auto

-- ── Safety / failure tests ─────────────────────────────────────────────────

-- Non-Tendsto goal must be rejected
example : True := by
  fail_if_success limit_auto
  trivial

-- t/t is indeterminate — must refuse
example : True := by
  fail_if_success (have : Tendsto (fun x : ℝ => x / x) (𝓝 1) (𝓝 1) := by limit_auto)
  trivial

-- (x-1)/(x-1) is indeterminate — must refuse (spec edge case)
example : True := by
  fail_if_success
    (have : Tendsto (fun x : ℝ => (x - 1) / (x - 1)) (𝓝 1) (𝓝 1) := by limit_auto)
  trivial

-- t/0 is indeterminate — must refuse
example : True := by
  fail_if_success (have : Tendsto (fun x : ℝ => x / 0) (𝓝 0) (𝓝 0) := by limit_auto)
  trivial

-- Unsupported pattern must fail (spec edge case: x/(x+1) → 1 at +∞)
example : True := by
  fail_if_success
    (have : Tendsto (fun x : ℝ => x / (x + 1)) atTop (𝓝 1) := by limit_auto)
  trivial

end Tests
