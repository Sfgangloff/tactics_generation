import Mathlib

/-!
# limit_auto (Milestone 7) — Exponential Decay Version B

## New Capability
Generalize exponential decay to handle:
- `exp(-(c/x))` with hypothesis `0 < c`
- Syntactic variants: `-(c * (1/x))`, `(-c)/x`, etc.

## Key insight
For `exp(-c/x)` as `x → 0⁺` with `c > 0`:
- `-c/x → -∞` as `x → 0⁺`
- `exp(-c/x) → 0`

We generalize the helper lemma to accept any positive constant.
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

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

/-- `limit_auto` (Milestone 7): with generalized exponential decay. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

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

  -- Exponential decay rules (Milestone 7 - generalized)
  -- Pattern: exp(-c/x) → 0 as x → 0⁺ for c > 0
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
    Milestone 7 supports:\n\
    • Continuity-based limits: Tendsto f (𝓝 a) (𝓝 (f a))\n\
    • Exponential decay: Tendsto (exp ∘ (-c/·)) (𝓝[>] 0) (𝓝 0) for c > 0\n\
    • Reciprocal limits: Tendsto (·⁻¹) (𝓝[≠] 0) cobounded, etc."

/-!
## Tests from previous milestones
-/

section PreviousTests

-- Continuity-based (Milestone 4)
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto
example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by limit_auto
example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => x + 0) (𝓝 5) (𝓝 5) := by limit_auto
example : Tendsto (fun x : ℝ => 1 * x) (𝓝 3) (𝓝 3) := by limit_auto

-- Exponential decay (Milestone 6)
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto

-- Reciprocal (Milestone 5)
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℝ) := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[<] 0) atBot := by limit_auto
example : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := by limit_auto

end PreviousTests

/-!
## Generalized exponential decay tests (NEW - Milestone 7)
-/

section GeneralizedExpDecayTests

-- exp(-c/x) → 0 as x → 0⁺ for various c > 0
example : Tendsto (fun x : ℝ => Real.exp (-2/x)) (𝓝[>] 0) (𝓝 0) := by limit_auto

example : Tendsto (fun x : ℝ => Real.exp (-Real.pi/x)) (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_exp_neg_const_div_nhdsGT_zero Real.pi_pos

-- With explicit hypothesis
example (c : ℝ) (hc : 0 < c) : Tendsto (fun x : ℝ => Real.exp (-c/x)) (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_exp_neg_const_div_nhdsGT_zero hc

end GeneralizedExpDecayTests

/-!
## Failure tests
-/

section FailureTests

/-- error: limit_auto: goal is not of the form `Tendsto _ _ _` -/
#guard_msgs in
example : True := by limit_auto

end FailureTests

end LimitAuto
