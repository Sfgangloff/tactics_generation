import Mathlib

/-!
# limit_auto (Milestone 2) — Strict Continuity Rule

## New Capability
Proves goals of the exact form:

    Tendsto f (𝓝 a) (𝓝 (f a))

whenever `fun_prop` can produce `ContinuousAt f a`.

## Important Constraints
- Does NOT attempt simp rewriting yet (that's Milestone 3)
- Requires the target literally to be `𝓝 (f a)`

## Why This Comes First
- Deterministic
- Mathematically clean
- Creates a reliable baseline rule
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

/-- `limit_auto` (Milestone 2): strict continuity rule. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

  -- Try to apply ContinuousAt.tendsto
  -- This only works if the goal has the exact shape `Tendsto f (𝓝 a) (𝓝 (f a))`
  try
    evalTactic (← `(tactic| refine ContinuousAt.tendsto ?_))
  catch _ =>
    throwError "limit_auto: unsupported Tendsto goal.\n\
      This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`."

  -- Prove the ContinuousAt goal using fun_prop
  try
    evalTactic (← `(tactic| fun_prop))
  catch _ =>
    throwError "limit_auto: could not prove ContinuousAt using fun_prop"

/-!
## Tests
-/

section Tests

/-! ### Goals with exact shape `Tendsto f (𝓝 a) (𝓝 (f a))` should succeed -/

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

example : Tendsto (fun x : ℝ => x^2) (𝓝 3) (𝓝 ((fun x : ℝ => x^2) 3)) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.sin x) (𝓝 0) (𝓝 ((fun x : ℝ => Real.sin x) 0)) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.exp x) (𝓝 1) (𝓝 ((fun x : ℝ => Real.exp x) 1)) := by
  limit_auto

/-! ### Goals where target is simplified (e.g., `𝓝 3` instead of `𝓝 (2+1)`) should FAIL -/

/-- error: limit_auto: unsupported Tendsto goal.
This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

-- Reference proof for the above (to be automated in Milestone 3)
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  have h := (by fun_prop : ContinuousAt (fun x : ℝ => x + 1) 2).tendsto
  convert h using 1
  norm_num

/-! ### Non-continuity goals should fail -/

/-- error: limit_auto: unsupported Tendsto goal.
This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/-- error: limit_auto: unsupported Tendsto goal.
This milestone only proves goals of the form `Tendsto f (𝓝 a) (𝓝 (f a))`. -/
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
