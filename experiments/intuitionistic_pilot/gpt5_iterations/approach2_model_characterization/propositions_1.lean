/- Attempt to generate a uniform tactic for implicational formulas of intuitionistic propositional logic.
Here, instead of prompting the model to directly generate a uniform tactic, we ask it to explain the examples and then explain a way to
generate a common tactic before writing it in lean.

As we can see, it infers a very restricted form of propositions, but the tactic is much cleaner.
-/

import Lean
open Lean Meta Elab.Tactic

/--
`proj_from_args`:
attempts to solve goals of the form `P₁ → ... → Pₙ → Pⱼ`
with `Pⱼ` already present among the hypotheses,
by introducing all arrows and then using `assumption`.
-/
def proj_from_args : TacticM Unit := do
  evalTactic (← `(tactic| intros; assumption))

-- Same code for all three
theorem propfmls_2_2_1 (A B : Prop) : A → B → B := by
  run_tac proj_from_args

theorem propfmls_2_2_2 (A : Prop) : A → A → A := by
  run_tac proj_from_args

theorem propfmls_2_2_3 (A B : Prop) : A → B → A := by
  run_tac proj_from_args
