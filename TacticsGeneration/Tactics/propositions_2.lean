import Lean
open Lean Meta Elab Tactic

/-- Introduce all arrows/foralls; then
    (1) solve if a freshly introduced local has the target type;
    (2) else, if there is `h : ∀ x : X, B x` and `e : X` among those locals
        with `B e` definitionally equal to the target, solve using `h e`. -/
def intro_all_then_assumption : TacticM Unit := do
  let g0 ← getMainGoal
  let (fs, g) ← g0.intros
  replaceMainGoal [g]
  withMainContext do
    let locals : Array Expr := fs.map mkFVar
    let tgt ← whnf (← g.getType)

    -- (1) exact match among introduced locals
    for e in locals do
      let ty ← whnf (← inferType e)
      if (← isDefEq ty tgt) then
        g.assign e
        setGoals []
        return

    -- (2) one-step functional case: use some h : ∀ x : X, B x with e : X so that B e ≃ tgt
    for h in locals do
      let hty ← whnf (← inferType h)
      match hty with
      | Expr.forallE _ X body _ =>
          for e in locals do
            let exTy ← whnf (← inferType e)
            if (← isDefEq exTy X) then
              let cod ← whnf (body.instantiate1 e)
              if (← isDefEq cod tgt) then
                g.assign (mkApp h e)
                setGoals []
                return
      | _ => pure ()

    throwError "intro_all_then_assumption: no introduced hypothesis matches the goal"

-- Your example stays unchanged
theorem t1 (A B : Prop) : A → B → A := by
  run_tac intro_all_then_assumption

theorem t2 (A B : Prop) : A → B → B := by
  run_tac intro_all_then_assumption
theorem t3 (A : Prop)   : A → A → A := by
  run_tac intro_all_then_assumption

theorem propfmls_3_4_4 (A B : Prop) : ((A → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_4_5 (A : Prop) : ((A → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_4_6 (A B : Prop) : ((A → B) → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_1 (A B C : Prop) : (A → B → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_2 (A B : Prop) : (A → B → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_3 (A B : Prop) : (A → A → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_4 (A B : Prop) : (A → B → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_5 (A : Prop) : (A → A → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_6 (A B C : Prop) : (A → B → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_7 (A B : Prop) : (A → A → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_8 (A B : Prop) : (A → B → A → B) :=by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_9 (A B C : Prop) : (A → B → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_10 (A B : Prop) : (A → B → B → A) := by
  run_tac intro_all_then_assumption
