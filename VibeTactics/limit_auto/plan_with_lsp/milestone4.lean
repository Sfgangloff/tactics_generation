import Mathlib

/-!
# limit_auto (Milestone 4) — Normalization Pass

## New Capability
Before dispatching rules, run a lightweight normalization step.

## Goals
- Improve pattern matching
- Avoid duplicating rules for syntactic variants
- Remain predictable (no aggressive simp)

## Examples of Good Rewrites
- `1 / x` → `x⁻¹`
- trivial arithmetic (`x + 0`, `(-1) * t`, etc.)
- definitional equalities

## Avoid
- heavy algebra
- rewriting that may expand expressions
- unbounded simp calls

This milestone strengthens ALL later rules.
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

/-- Normalization simp lemmas for limit expressions.
    These should be conservative and not expand expressions. -/
def normSimpLemmas : Array Name := #[
  ``one_div,           -- 1 / x = x⁻¹
  ``add_zero,          -- x + 0 = x
  ``zero_add,          -- 0 + x = x
  ``mul_one,           -- x * 1 = x
  ``one_mul,           -- 1 * x = x
  ``mul_zero,          -- x * 0 = 0
  ``zero_mul,          -- 0 * x = 0
  ``neg_neg,           -- -(-x) = x
  ``sub_zero,          -- x - 0 = x
  ``neg_zero,          -- -0 = 0
  ``inv_one            -- 1⁻¹ = 1
]

/-- `limit_auto` (Milestone 4): with normalization pass. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

  -- Normalization pass: apply conservative simp lemmas
  -- Use `try` because it may not change anything
  try
    evalTactic (← `(tactic|
      simp only [one_div, add_zero, zero_add, mul_one, one_mul,
                 mul_zero, zero_mul, neg_neg, sub_zero, neg_zero, inv_one]
    ))
  catch _ => pure ()

  -- Now try the rules from Milestone 3
  -- Use `fun_prop (disch := norm_num)` to handle side conditions like `2 ≠ 0`
  try
    evalTactic (← `(tactic|
      first
      | exact ContinuousAt.tendsto (by fun_prop (disch := norm_num))
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by norm_num)
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by simp)
      | refine tendsto_of_continuousAt_eq (by fun_prop (disch := norm_num)) (by ring)
    ))
  catch _ =>
    throwError "limit_auto: unsupported Tendsto goal.\n\
      This milestone handles goals of the form `Tendsto f (𝓝 a) (𝓝 b)` \
      where `b = f a` can be proven by simp, norm_num, or ring."

/-!
## Tests
-/

section Tests

/-! ### Previous tests should still work -/

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by
  limit_auto

/-! ### Tests benefiting from normalization (NEW) -/

-- `1/x` normalized to `x⁻¹` in the function
example : Tendsto (fun x : ℝ => 1/x + 0) (𝓝 2) (𝓝 ((fun x : ℝ => x⁻¹) 2)) := by
  limit_auto

-- `x + 0` simplified
example : Tendsto (fun x : ℝ => x + 0) (𝓝 5) (𝓝 5) := by
  limit_auto

-- `1 * x` simplified
example : Tendsto (fun x : ℝ => 1 * x) (𝓝 3) (𝓝 3) := by
  limit_auto

/-! ### Non-continuity goals should still fail -/

/-- error: limit_auto: unsupported Tendsto goal.
This milestone handles goals of the form `Tendsto f (𝓝 a) (𝓝 b)` where `b = f a` can be proven by simp, norm_num, or ring. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/-- error: limit_auto: unsupported Tendsto goal.
This milestone handles goals of the form `Tendsto f (𝓝 a) (𝓝 b)` where `b = f a` can be proven by simp, norm_num, or ring. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

/-! ### Non-Tendsto goal -/

/-- error: limit_auto: goal is not of the form `Tendsto _ _ _` -/
#guard_msgs in
example : True := by
  limit_auto

end Tests

end LimitAuto
