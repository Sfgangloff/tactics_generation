import Mathlib

/-!
# limit_auto (Milestone 1) — Skeleton and Principled Failure

## Behavior
- If the goal is not `Tendsto _ _ _`, fail with a clear message.
- If it is a `Tendsto` goal but unsupported, fail with "unsupported shape".

## Architecture (future-proof)
The dispatcher structure:
1. normalize goal
2. try rules in fixed order
3. fail

This dispatcher remains unchanged throughout the project.
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

/-- `limit_auto` (Milestone 1): recognizes `Tendsto` goals and otherwise fails. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  -- Check if goal is of form `Tendsto _ _ _`
  if tgt.isAppOf ``Filter.Tendsto then
    throwError "limit_auto: recognized `Tendsto` goal but no rules apply (unsupported shape)"
  else
    throwError "limit_auto: goal is not of the form `Tendsto _ _ _`"

/-!
## Tests

At Milestone 1, `limit_auto` should fail on all tests.
For true statements, we provide reference proofs so the file compiles.
-/

section Tests

/-! ### Continuity-based examples (true statements) -/

/-- error: limit_auto: recognized `Tendsto` goal but no rules apply (unsupported shape) -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

-- Reference proof for the above
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  have hcont : ContinuousAt (fun x : ℝ => x + 1) 2 := by fun_prop
  have h := hcont.tendsto
  simp only at h
  convert h using 1
  norm_num

/-! ### Reciprocal/cobounded example -/

/-- error: limit_auto: recognized `Tendsto` goal but no rules apply (unsupported shape) -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/-! ### Exponential decay example -/

/-- error: limit_auto: recognized `Tendsto` goal but no rules apply (unsupported shape) -/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

/-! ### Non-Tendsto goal (should fail differently) -/

/-- error: limit_auto: goal is not of the form `Tendsto _ _ _` -/
#guard_msgs in
example : True := by
  limit_auto

end Tests

end LimitAuto
