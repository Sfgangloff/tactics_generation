import Mathlib

/-!
# limit_auto (Milestone 5) — Exponential Decay Limits

## New Capability
Handle limits of the form `exp(-c/x) → 0` as `x → 0⁺`.

## Mathematical Background
For `exp(-1/x)` as `x → 0⁺`:
- As `x → 0⁺`, we have `1/x → +∞`
- So `-1/x → -∞`
- Thus `exp(-1/x) → 0`

Key lemmas used:
- `Real.tendsto_exp_atBot`: `exp → 0` as arg → -∞
- `tendsto_inv_nhdsGT_zero`: `x⁻¹ → +∞` as `x → 0⁺`
- `tendsto_neg_atTop_atBot`: `-x → -∞` as `x → +∞`
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

/-- Helper lemma for exponential decay: `-1/x → -∞` as `x → 0⁺`. -/
theorem tendsto_neg_one_div_nhdsGT_zero_atBot :
    Tendsto (fun x : ℝ => -1/x) (𝓝[>] 0) atBot := by
  have h : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun x : ℝ => -x) atTop atBot := tendsto_neg_atTop_atBot
  convert h2.comp h using 1
  ext x
  simp only [Function.comp_apply]
  field_simp

/-- `limit_auto` (Milestone 5): with exponential decay support. -/
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

  -- Exponential decay rules (Milestone 5)
  -- Pattern: exp(-c/x) → 0 as x → 0⁺
  try
    evalTactic (← `(tactic|
      first
      | exact Real.tendsto_exp_atBot.comp tendsto_neg_one_div_nhdsGT_zero_atBot
      | refine (Real.tendsto_exp_atBot).comp ?_
        exact tendsto_neg_one_div_nhdsGT_zero_atBot
    ))
    return
  catch _ => pure ()

  throwError "limit_auto: unsupported Tendsto goal.\n\
    Milestone 5 supports:\n\
    • Continuity-based limits: Tendsto f (𝓝 a) (𝓝 (f a))\n\
    • Exponential decay: Tendsto (exp ∘ (-1/·)) (𝓝[>] 0) (𝓝 0)"

/-!
## Tests from previous milestones
-/

section PreviousTests

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto
example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by limit_auto
example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by limit_auto
example : Tendsto (fun x : ℝ => 1/x + 0) (𝓝 2) (𝓝 ((fun x : ℝ => x⁻¹) 2)) := by limit_auto
example : Tendsto (fun x : ℝ => x + 0) (𝓝 5) (𝓝 5) := by limit_auto
example : Tendsto (fun x : ℝ => 1 * x) (𝓝 3) (𝓝 3) := by limit_auto

end PreviousTests

/-!
## Exponential decay tests (NEW)
-/

section ExponentialDecayTests

-- Basic exponential decay as x → 0⁺
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝[>] 0) (𝓝 0) := by
  limit_auto

end ExponentialDecayTests

/-!
## Non-Tendsto goals should still fail appropriately
-/

section FailureTests

/-- error: limit_auto: goal is not of the form `Tendsto _ _ _` -/
#guard_msgs in
example : True := by limit_auto

end FailureTests

end LimitAuto
