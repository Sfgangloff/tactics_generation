import Mathlib

/-!
# limit_auto (Milestone 5)

Adds the reciprocal/cobounded rule (for any `NormedField 𝕜`) on top of Milestone 4.

Rule added:

    Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[≠] 0) cobounded
    Tendsto (fun x : 𝕜 => x⁻¹) cobounded (𝓝[≠] 0)

We keep the conservative normalization pass (Milestone 4) and then:
  1) try reciprocal/cobounded lemmas (Milestone 5)
  2) fall back to continuity + simp-equality (Milestone 3/4)

Still out of scope (should fail with a clear message):
- exponential decay goals (Milestone 6+)
- anything not of the form `Tendsto _ _ _`
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

/-- Helper lemma for Milestone 3+. -/
theorem tendsto_of_continuousAt_eq
    {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {a : α} {b : β}
    (hcont : ContinuousAt f a) (hb : b = f a) :
    Tendsto f (𝓝 a) (𝓝 b) := by
  simpa [hb] using hcont.tendsto

/-- Conservative normalization step (Milestone 4), implemented as explicit rewrites. -/
macro "limit_auto_normalize" : tactic =>
  `(tactic|
    repeat
      first
      | rw [one_div]        -- 1 / x → x⁻¹
      | rw [add_zero]       -- x + 0 → x
      | rw [zero_add]       -- 0 + x → x
      | rw [sub_zero]       -- x - 0 → x
      | rw [zero_sub]       -- 0 - x → -x
      | rw [neg_one_mul]    -- (-1) * x → -x
      | rw [mul_neg_one]    -- x * (-1) → -x
  )

/-- `limit_auto` (Milestone 5). -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto (Milestone 5): goal is not of the form `Tendsto _ _ _`."

  let failMsg :=
    "limit_auto (Milestone 5): unsupported Tendsto goal.\n\
    This milestone supports:\n\
    • reciprocal/cobounded goals for `x ↦ x⁻¹` over any `NormedField`\n\
    • continuity goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when, after a conservative\n\
      normalization pass, `simp` can show `b = f a`."

  try
    -- Milestone 4: normalize syntactically.
    evalTactic (← `(tactic| limit_auto_normalize))

    -- Milestone 5: reciprocal / cobounded rule (deterministic, no search)
    -- Force a match so the type `𝕜` is fixed by the goal before applying the lemma.
    try
      evalTactic (← `(tactic|
        first
        | (
            match_target
              Tendsto (fun x : ?𝕜 => x⁻¹) (𝓝[≠] (0 : ?𝕜)) (cobounded : Filter ?𝕜)
            simpa using
              (tendsto_inv₀_cobounded :
                Tendsto (fun x : ?𝕜 => x⁻¹) (𝓝[≠] (0 : ?𝕜)) (cobounded : Filter ?𝕜))
          )
        | (
            match_target
              Tendsto (fun x : ?𝕜 => x⁻¹) (cobounded : Filter ?𝕜) (𝓝[≠] (0 : ?𝕜))
            simpa using
              (tendsto_inv_cobounded :
                Tendsto (fun x : ?𝕜 => x⁻¹) (cobounded : Filter ?𝕜) (𝓝[≠] (0 : ?𝕜)))
          )
      ))
      return
    catch _ =>
      pure ()

    -- Milestone 3: continuity + equality b = f a.
    evalTactic (← `(tactic|
      refine (tendsto_of_continuousAt_eq (f := _) (a := _) (b := _) ?_ ?_)
    ))

    -- Goal 1: continuity
    evalTactic (← `(tactic|
      first
      | fun_prop
      | continuity
    ))

    -- Goal 2: equality b = f a (after normalization)
    evalTactic (← `(tactic|
      first
      | (simp [one_div]; norm_num)
      | simp [one_div]
      | norm_num
    ))
  catch _ =>
    throwError failMsg

section Tests

-- From Milestone 3/4: still succeeds.
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  limit_auto

example :
    Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

-- From Milestone 4: normalization examples.
example : Tendsto (fun x : ℝ => x + 0) (𝓝 2) (𝓝 2) := by
  limit_auto

example :
    Tendsto (fun x : ℝ => 1 / x) (𝓝 2) (𝓝 ((fun x : ℝ => 1 / x) 2)) := by
  limit_auto

example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

example : Tendsto (fun x : ℝ => x⁻¹) (cobounded : Filter ℝ) (𝓝[≠] 0) := by
  limit_auto

#check cobounded
#check tendsto_inv₀_cobounded
#check tendsto_inv_cobounded
#check Filter.tendsto_inv₀_cobounded
#check Filter.tendsto_inv_cobounded

/--
error: limit_auto (Milestone 5): unsupported Tendsto goal.
This milestone supports:
• reciprocal/cobounded goals for `x ↦ x⁻¹` over any `NormedField`
• continuity goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when, after a conservative normalization pass, `simp` can show `b = f a`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

end Tests

end LimitAuto
