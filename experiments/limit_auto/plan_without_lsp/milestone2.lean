import Mathlib

/-!
# limit_auto (Milestone 2)

New capability (strict continuity rule only):

Proves goals of the exact form

    Tendsto f (𝓝 a) (𝓝 (f a))

whenever `by continuity` can produce `ContinuousAt f a`.

Important: no simp-based rewriting of the target yet (Milestone 3).
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

/-- `limit_auto` (Milestone 2). -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto (Milestone 2): goal is not of the form `Tendsto _ _ _`."

  let failMsg :=
    "limit_auto (Milestone 2): unsupported Tendsto goal.\n\
    This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`."

  -- strict-shape check by unification
  try
    evalTactic (← `(tactic|
      refine (ContinuousAt.tendsto ?_)
    ))
  catch _ =>
    throwError failMsg

  -- try to prove the ContinuousAt goal
  -- `fun_prop` is typically the reliable tool here.
  evalTactic (← `(tactic|
    fun_prop
  ))






section Tests

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  fail_if_success limit_auto
  have hcont : ContinuousAt (fun x : ℝ => x + 1) 2 := by
    simpa using (continuousAt_id.add continuousAt_const)
  have ht :
      Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) :=
    hcont.tendsto
  simpa using (by
    simpa [show ((fun x : ℝ => x + 1) 2) = (3:ℝ) by norm_num] using ht)

example : Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  fail_if_success limit_auto
  have hinner : ContinuousAt (fun x : ℝ => x^2 + 1) 0 := by
    simpa using ((continuousAt_id.pow 2).add continuousAt_const)
  have hcont : ContinuousAt (fun x : ℝ => Real.sin (x^2 + 1)) 0 := by
    exact (Real.continuous_sin.continuousAt).comp (x := 0) hinner
  have ht :
      Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0)
        (𝓝 ((fun x : ℝ => Real.sin (x^2 + 1)) 0)) :=
    hcont.tendsto
  simpa using ht

-- strict shape: should succeed
example :
    Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

/--
error: limit_auto (Milestone 2): unsupported Tendsto goal.
This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/--
error: limit_auto (Milestone 2): unsupported Tendsto goal.
This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

end Tests
end LimitAuto
