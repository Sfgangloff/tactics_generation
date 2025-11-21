import Lean
open Lean Meta Elab.Tactic

/--
`intro_all_then_assumption`:

1. Repeatedly introduce all outer `→` binders (`repeat intro`).
2. Try to solve the resulting goal from the local context:
   - first by direct projection (some hypothesis has exactly the goal type),
   - then by one-step application: if there is `f : P → Q` and `a : P`
     and the goal is `Q`, solve it with `f a`.

If none of these patterns applies, the tactic fails.
-/
def intro_all_then_assumption : TacticM Unit := do
  /- Step 1: introduce all arrow binders -/
  evalTactic (← `(tactic| repeat intro))

  /- Step 2 + 3: solve from context -/
  withMainContext do
    let g      ← getMainGoal
    let goalTy ← getMainTarget
    let lctx   ← getLCtx

    /- 2. Direct projection: some hypothesis has exactly the goal type -/
    for d in lctx do
      if !d.isImplementationDetail then
        if (← isDefEq d.type goalTy) then
          g.assign (mkFVar d.fvarId)
          setGoals []
          return

    /- 3. One-step application: f : P → Q and a : P -/
    for d in lctx do
      if !d.isImplementationDetail then
        match d.type with
        | Expr.forallE _ dom body _ =>
            -- we only handle non-dependent arrows P → Q (no loose bound vars)
            if body.hasLooseBVars then
              pure ()
            else if (← isDefEq body goalTy) then
              -- search argument a : dom in the context
              for d2 in lctx do
                if !d2.isImplementationDetail then
                  if (← isDefEq d2.type dom) then
                    let f := mkFVar d.fvarId
                    let a := mkFVar d2.fvarId
                    g.assign (mkApp f a)
                    setGoals []
                    return
        | _ => pure ()

    /- If we reach here, we failed to solve the goal -/
    throwError "intro_all_then_assumption: could not solve the goal"

-- Your example stays unchanged
theorem t1 (A B : Prop) : A → B → A := by
  run_tac intro_all_then_assumption
theorem t2 (A B : Prop) : A → B → B := by
  run_tac intro_all_then_assumption
theorem t3 (A : Prop)   : A → A → A := by
  run_tac intro_all_then_assumption

-- theorem propfmls_3_1_1 (A B : Prop) : (((A → A) → B) → B) := by
--   run_tac intro_all_then_assumption
-- theorem propfmls_3_1_2 (A : Prop) : (((A → A) → A) → A) := by
--   run_tac intro_all_then_assumption

theorem propfmls_3_3_1 (A B C : Prop) : (A → (B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_2 (A B : Prop) : (A → (A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_3 (A B : Prop) : (A → (B → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_4 (A B : Prop) : (A → (B → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_5 (A : Prop) : (A → (A → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_6 (A B : Prop) : (A → (A → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_4_1 (A B C : Prop) : ((A → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_4_2 (A B : Prop) : ((A → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_4_3 (A B : Prop) : ((A → A) → B → B) := by
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
