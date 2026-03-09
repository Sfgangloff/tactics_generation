import Mathlib

/-!
# limit_auto (Milestone 4)

Adds a conservative normalization pass before the Milestone 3 continuity rule.

Normalization is implemented via explicit rewrites (no broad simp sets).
Continuity discharge is `fun_prop` with a fallback to `continuity` (needed e.g. for `inv`).
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
      | (rw [one_div])               -- 1 / x → x⁻¹
      | (rw [add_zero])              -- x + 0 → x
      | (rw [zero_add])              -- 0 + x → x
      | (rw [sub_zero])              -- x - 0 → x
      | (rw [zero_sub])              -- 0 - x → -x
      | (rw [neg_one_mul])           -- (-1) * x → -x
      | (rw [mul_neg_one])           -- x * (-1) → -x
  )

/-- `limit_auto` (Milestone 4). -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto (Milestone 4): goal is not of the form `Tendsto _ _ _`."

  let failMsg :=
    "limit_auto (Milestone 4): unsupported Tendsto goal.\n\
    This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when, after a\n\
    conservative normalization pass, `simp` can show `b = f a`."

  try
    -- Normalize first (Milestone 4)
    evalTactic (← `(tactic| limit_auto_normalize))

    -- Milestone 3: reduce to continuity + identifying equality
    evalTactic (← `(tactic|
      refine (tendsto_of_continuousAt_eq (f := _) (a := _) (b := _) ?_ ?_)
    ))

    -- Goal 1: continuity (fallback to `continuity` needed for e.g. inv)
    evalTactic (← `(tactic|
      first
      | fun_prop
      | continuity
    ))

    -- Goal 2: identifying equality (allow one_div so `1/x` and `x⁻¹` align)
    evalTactic (← `(tactic|
      first
      | (simp [one_div]; norm_num)
      | simp [one_div]
      | norm_num
    ))
  catch _ =>
    throwError failMsg

section Tests


-- From Milestone 3: still succeeds.
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  limit_auto

example :
    Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

-- New (Milestone 4): trivial normalization `x + 0`.
example : Tendsto (fun x : ℝ => x + 0) (𝓝 2) (𝓝 2) := by
  limit_auto

-- New (Milestone 4): `1/x` normalization (needs `continuity` fallback for inv).
example :
    Tendsto (fun x : ℝ => 1 / x) (𝓝 2) (𝓝 ((fun x : ℝ => 1 / x) 2)) := by
  limit_auto

/--
error: limit_auto (Milestone 4): unsupported Tendsto goal.
This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when, after a
conservative normalization pass, `simp` can show `b = f a`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/--
error: limit_auto (Milestone 4): unsupported Tendsto goal.
This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when, after a
conservative normalization pass, `simp` can show `b = f a`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

end Tests

end LimitAuto
