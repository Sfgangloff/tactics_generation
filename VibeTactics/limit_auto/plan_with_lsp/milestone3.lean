import Mathlib

/-!
# limit_auto (Milestone 3) — Robust Continuity via Simp Equality

## Refinement of Milestone 2
Now allows targets:

    Tendsto f (𝓝 a) (𝓝 b)

provided `simp` or `norm_num` can prove: `b = f a`

## Implementation
Uses a helper lemma that combines ContinuousAt.tendsto with filter equality.
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

/-- `limit_auto` (Milestone 3): continuity rule with simp-based target matching. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

  -- Try applying the helper lemma with fun_prop for continuity and norm_num/simp for equality
  try
    evalTactic (← `(tactic|
      first
      | exact ContinuousAt.tendsto (by fun_prop)
      | refine tendsto_of_continuousAt_eq (by fun_prop) (by norm_num)
      | refine tendsto_of_continuousAt_eq (by fun_prop) (by simp)
      | refine tendsto_of_continuousAt_eq (by fun_prop) (by ring)
    ))
  catch _ =>
    throwError "limit_auto: unsupported Tendsto goal.\n\
      This milestone handles goals of the form `Tendsto f (𝓝 a) (𝓝 b)` \
      where `b = f a` can be proven by simp, norm_num, or ring."

/-!
## Tests
-/

section Tests

/-! ### Exact shape (Milestone 2 tests should still work) -/

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 ((fun x : ℝ => x^2) 3)) := by
  limit_auto

/-! ### Simp-convertible targets (NEW in Milestone 3) -/

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 9) := by
  limit_auto

example : Tendsto (fun x : ℝ => 2 * x) (𝓝 5) (𝓝 10) := by
  limit_auto

example : Tendsto (fun x : ℝ => x - 1) (𝓝 4) (𝓝 3) := by
  limit_auto

/-! ### Composition examples -/

example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 0) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.cos x) (𝓝 0) (𝓝 1) := by
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
