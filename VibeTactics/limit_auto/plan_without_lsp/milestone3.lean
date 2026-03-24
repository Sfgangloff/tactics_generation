import Mathlib

/-!
# limit_auto (Milestone 3)

New capability (robust continuity via simp equality):

Proves goals of the form

    Tendsto f (𝓝 a) (𝓝 b)

provided `simp` (and, for numeric side-goals, `norm_num`) can prove

    b = f a

and `fun_prop` can prove `ContinuousAt f a`.

Milestone 2 becomes a special case of this one.

Still out of scope (should fail with a clear message):
- reciprocal / cobounded goals
- exponential decay goals
- anything not of the form `Tendsto _ _ _`
-/

namespace LimitAuto

open scoped Topology
open Filter
open Lean Elab Tactic Meta

/-- Helper lemma for Milestone 3. -/
theorem tendsto_of_continuousAt_eq
    {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {a : α} {b : β}
    (hcont : ContinuousAt f a) (hb : b = f a) :
    Tendsto f (𝓝 a) (𝓝 b) := by
  simpa [hb] using hcont.tendsto

/-- `limit_auto` (Milestone 3). -/
elab "limit_auto" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)

  unless tgt.isAppOf ``Filter.Tendsto do
    throwError "limit_auto (Milestone 3): goal is not of the form `Tendsto _ _ _`."

  let failMsg :=
    "limit_auto (Milestone 3): unsupported Tendsto goal.\n\
    This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when `simp` can show `b = f a`."

  try
    -- Milestone 3: reduce to (ContinuousAt f a) and (b = f a)
    evalTactic (← `(tactic|
      refine (tendsto_of_continuousAt_eq (f := _) (a := _) (b := _) ?_ ?_)
    ))

    -- Goal 1: continuity
    evalTactic (← `(tactic| fun_prop))

    -- Goal 2: identifying equality
    -- `simp` handles definitional reductions; `norm_num` closes numeric arithmetic.
    -- We avoid `try` (syntax differences) and instead use `first`.
    evalTactic (← `(tactic|
      first
      | (simp; norm_num)
      | simp
      | norm_num
    ))
  catch _ =>
    throwError failMsg

section Tests

-- Previously failing in Milestone 2 (target not literally `𝓝 (f a)`), now succeeds.
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by
  limit_auto

example : Tendsto (fun x : ℝ => Real.sin (x^2 + 1)) (𝓝 0) (𝓝 (Real.sin 1)) := by
  limit_auto

-- Strict shape: still succeeds
example :
    Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 ((fun x : ℝ => x + 1) 2)) := by
  limit_auto

/--
error: limit_auto (Milestone 3): unsupported Tendsto goal.
This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when `simp` can show `b = f a`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) (cobounded : Filter ℝ) := by
  limit_auto

/--
error: limit_auto (Milestone 3): unsupported Tendsto goal.
This milestone proves goals of the form `Tendsto f (𝓝 a) (𝓝 b)` when `simp` can show `b = f a`.
-/
#guard_msgs in
example : Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0) := by
  limit_auto

end Tests

end LimitAuto
