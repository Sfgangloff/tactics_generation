import Mathlib

/-!
# limit_auto (Milestone 1)

Milestone 1 guarantees only:
- the tactic `limit_auto` exists,
- it recognizes when the goal is a `Filter.Tendsto` statement,
- it fails with a clear error message (no proving power yet).

This file also contains the tests listed in the specification.
At Milestone 1, `limit_auto` is expected to fail on all those tests.
For the tests that are *true*, we additionally provide a reference proof so the file compiles.
-/

namespace LimitAuto

open scoped Topology
open Filter

open Lean Elab Tactic Meta

/-- `limit_auto` (Milestone 1): recognizes `Tendsto` goals and otherwise fails. -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isAppOf ``Filter.Tendsto then
    throwError "limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet."
  else
    throwError "limit_auto (Milestone 1): goal is not of the form `Tendsto _ _ _`."

/-!
## Tests from the specification
-/

section Tests

/-! ### Continuity-based examples (true) -/

example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  fail_if_success limit_auto
  -- reference proof (close to what later milestones will automate)
  have hcont : ContinuousAt (fun x : ℝ => x + 1) 2 := by
    simpa using (continuousAt_id.add continuousAt_const)

  have ht :
      Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) :=
    hcont.tendsto

  -- turns `𝓝 (2 + 1)` into `𝓝 3`
  simpa using (by
    simpa [show ((fun x : ℝ => x + 1) 2) = (3:ℝ) by norm_num] using ht)

example : Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  fail_if_success limit_auto
  have hinner : ContinuousAt (fun x : ℝ => x^2 + 1) 0 := by
    simpa using ((continuousAt_id.pow 2).add continuousAt_const)

  have hcont : ContinuousAt (fun x : ℝ => Real.sin (x^2 + 1)) 0 := by
    -- sin is continuous everywhere; compose with the inner function
    exact (Real.continuous_sin.continuousAt).comp (x := 0) hinner

  have ht :
      Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0)
        (𝓝 ((fun x : ℝ => Real.sin (x^2 + 1)) 0)) :=
    hcont.tendsto

  simpa using ht

/-! ### Reciprocal/cobounded example (intended to be solved later)

We only test that Milestone 1 fails with the expected message.
-/

/-- error: limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/-! ### Exponential decay example (intended to be solved later) -/

/-- error: limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

/-! ### Edge-case tests (should fail for the tactic)

Some of these are mathematically false (wrong filter), but at Milestone 1 we only check
that the tactic does not succeed.
-/

/-- error: limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => (x-1)/(x-1)) (𝓝 1) (𝓝 1) := by
  limit_auto

/-- error: limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) (𝓝 0) (𝓝 0) := by
  limit_auto

/-- error: limit_auto (Milestone 1): recognized a `Tendsto` goal but this milestone proves nothing yet. -/
#guard_msgs in
example : Tendsto (fun x : ℝ => x/(x+1)) atTop (𝓝 1) := by
  limit_auto

end Tests

end LimitAuto
