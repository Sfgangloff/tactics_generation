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

/-- Example stays unchanged and works with `run_tac`. -/
theorem t1 (A B : Prop) : A → B → A := by
  run_tac intro_all_then_assumption
theorem t2 (A B : Prop) : A → B → B := by
  run_tac intro_all_then_assumption
theorem t3 (A : Prop)   : A → A → A := by
  run_tac intro_all_then_assumption


theorem propfmls_3_1_1 (A B : Prop) : (((A → A) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_1_2 (A : Prop) : (((A → A) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_1 (A B C : Prop) : (A → (B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_2 (A B : Prop) : (A → (A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_3_3 (A B : Prop) : (A → (B → B) → A) := by
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
theorem propfmls_3_5_8 (A B : Prop) : (A → B → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_9 (A B C : Prop) : (A → B → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_3_5_10 (A B : Prop) : (A → B → B → A) := by
  run_tac intro_all_then_assumption

theorem propfmls_4_2_1 (A B C : Prop) : (((A → B → B) → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_2 (A B : Prop) : (((A → B → B) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_3 (A B : Prop) : (((A → A → A) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_4 (A B : Prop) : (((A → B → B) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_5 (A : Prop) : (((A → A → A) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_6 (A B C : Prop) : (((A → B → A) → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_7 (A B : Prop) : (((A → B → A) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_2_8 (A B : Prop) : (((A → B → A) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_1 (A B C D : Prop) : (A → ((B → C) → D) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_2 (A B C : Prop) : (A → ((A → B) → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_3 (A B C : Prop) : (A → ((B → C) → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_4 (A B C : Prop) : (A → ((B → B) → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_5 (A B C : Prop) : (A → ((B → A) → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_6 (A B : Prop) : (A → ((A → A) → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_7 (A B : Prop) : (A → ((B → A) → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_8 (A B C : Prop) : (A → ((B → C) → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_9 (A B : Prop) : (A → ((A → B) → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_10 (A B : Prop) : (A → ((B → B) → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_11 (A B C : Prop) : (A → ((B → C) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_12 (A B : Prop) : (A → ((A → B) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_13 (A B : Prop) : (A → ((B → B) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_14 (A B : Prop) : (A → ((B → A) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_15 (A : Prop) : (A → ((A → A) → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_16 (A B C : Prop) : (A → ((B → A) → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_17 (A B : Prop) : (A → ((B → A) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_18 (A B : Prop) : (A → ((A → A) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_19 (A B C : Prop) : (A → ((B → B) → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_4_20 (A B : Prop) : (A → ((B → B) → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_1 (A B C D : Prop) : (A → (B → C → D) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_2 (A B C : Prop) : (A → (A → B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_3 (A B C : Prop) : (A → (B → C → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_4 (A B C : Prop) : (A → (B → B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_5 (A B C : Prop) : (A → (B → A → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_6 (A B : Prop) : (A → (A → A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_7 (A B : Prop) : (A → (B → A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_8 (A B C : Prop) : (A → (B → C → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_9 (A B : Prop) : (A → (A → B → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_10 (A B : Prop) : (A → (B → B → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_11 (A B C : Prop) : (A → (B → C → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_12 (A B : Prop) : (A → (A → B → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_13 (A B : Prop) : (A → (B → B → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_14 (A B : Prop) : (A → (B → A → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_15 (A : Prop) : (A → (A → A → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_7_16 (A B : Prop) : (A → (A → A → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_1 (A B C D : Prop) : (A → B → (C → D) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_2 (A B C : Prop) : (A → A → (B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_3 (A B C : Prop) : (A → B → (C → A) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_4 (A B C : Prop) : (A → B → (A → C) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_5 (A B C : Prop) : (A → B → (B → C) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_6 (A B : Prop) : (A → A → (A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_7 (A B : Prop) : (A → B → (B → A) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_8 (A B C : Prop) : (A → B → (C → C) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_9 (A B : Prop) : (A → A → (B → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_10 (A B : Prop) : (A → B → (A → A) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_11 (A B C : Prop) : (A → B → (C → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_12 (A B : Prop) : (A → A → (B → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_13 (A B : Prop) : (A → B → (A → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_14 (A B : Prop) : (A → B → (B → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_15 (A : Prop) : (A → A → (A → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_16 (A B C D : Prop) : (A → B → (C → D) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_17 (A B C : Prop) : (A → B → (C → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_18 (A B C : Prop) : (A → B → (B → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_19 (A B C : Prop) : (A → B → (A → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_20 (A B : Prop) : (A → B → (A → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_21 (A B C : Prop) : (A → B → (C → C) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_22 (A B : Prop) : (A → B → (B → B) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_23 (A B C : Prop) : (A → B → (C → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_24 (A B : Prop) : (A → B → (B → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_25 (A B : Prop) : (A → B → (A → A) → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_26 (A B C : Prop) : (A → B → (B → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_27 (A B : Prop) : (A → A → (A → B) → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_9_28 (A B C : Prop) : (A → B → (A → C) → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_1 (A B C D : Prop) : (((A → B) → C) → D → D) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_2 (A B C : Prop) : (((A → B) → C) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_3 (A B C : Prop) : (((A → B) → A) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_4 (A B C : Prop) : (((A → A) → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_5 (A B C : Prop) : (((A → B) → C) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_6 (A B : Prop) : (((A → A) → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_7 (A B : Prop) : (((A → B) → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_8 (A B C : Prop) : (((A → B) → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_9 (A B : Prop) : (((A → B) → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_10 (A B : Prop) : (((A → A) → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_11 (A B C : Prop) : (((A → B) → C) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_12 (A B : Prop) : (((A → B) → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_13 (A B : Prop) : (((A → A) → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_14 (A B : Prop) : (((A → B) → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_15 (A : Prop) : (((A → A) → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_16 (A B C : Prop) : (((A → B) → C) → B → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_17 (A B : Prop) : (((A → B) → A) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_18 (A B : Prop) : (((A → A) → B) → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_19 (A B C : Prop) : (((A → A) → B) → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_10_20 (A B : Prop) : (((A → A) → A) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_1 (A B C D : Prop) : ((A → B → C) → D → D) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_2 (A B C : Prop) : ((A → B → C) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_3 (A B C : Prop) : ((A → B → A) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_4 (A B C : Prop) : ((A → A → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_5 (A B C : Prop) : ((A → B → C) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_6 (A B : Prop) : ((A → A → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_7 (A B : Prop) : ((A → B → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_8 (A B C : Prop) : ((A → B → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_9 (A B : Prop) : ((A → B → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_10 (A B : Prop) : ((A → A → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_11 (A B C : Prop) : ((A → B → C) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_12 (A B : Prop) : ((A → B → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_13 (A B : Prop) : ((A → A → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_14 (A B : Prop) : ((A → B → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_15 (A : Prop) : ((A → A → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_11_16 (A B : Prop) : ((A → A → B) → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_1 (A B C D : Prop) : (A → (B → C) → D → D) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_2 (A B C : Prop) : (A → (B → C) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_3 (A B C : Prop) : (A → (B → A) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_4 (A B C : Prop) : (A → (A → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_5 (A B C : Prop) : (A → (B → C) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_6 (A B : Prop) : (A → (A → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_7 (A B : Prop) : (A → (B → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_8 (A B C : Prop) : (A → (B → B) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_9 (A B : Prop) : (A → (B → B) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_10 (A B : Prop) : (A → (A → A) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_11 (A B C : Prop) : (A → (B → C) → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_12 (A B : Prop) : (A → (B → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_13 (A B : Prop) : (A → (A → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_14 (A B : Prop) : (A → (B → B) → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_15 (A : Prop) : (A → (A → A) → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_16 (A B C D : Prop) : (A → (B → C) → D → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_17 (A B C : Prop) : (A → (A → B) → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_18 (A B C : Prop) : (A → (B → C) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_19 (A B C : Prop) : (A → (B → B) → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_20 (A B C : Prop) : (A → (B → A) → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_21 (A B : Prop) : (A → (A → A) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_22 (A B : Prop) : (A → (B → A) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_23 (A B C : Prop) : (A → (B → C) → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_24 (A B : Prop) : (A → (A → B) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_25 (A B : Prop) : (A → (B → B) → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_26 (A B C : Prop) : (A → (B → C) → B → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_27 (A B : Prop) : (A → (A → B) → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_12_28 (A B C : Prop) : (A → (A → B) → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_1 (A B C D : Prop) : ((A → B) → C → D → D) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_2 (A B C : Prop) : ((A → B) → C → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_3 (A B C : Prop) : ((A → B) → A → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_4 (A B C : Prop) : ((A → A) → B → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_5 (A B C : Prop) : ((A → B) → C → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_6 (A B : Prop) : ((A → A) → B → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_7 (A B : Prop) : ((A → B) → A → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_8 (A B C : Prop) : ((A → B) → B → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_9 (A B : Prop) : ((A → B) → B → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_10 (A B : Prop) : ((A → A) → A → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_11 (A B C : Prop) : ((A → B) → C → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_12 (A B : Prop) : ((A → B) → A → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_13 (A B : Prop) : ((A → A) → B → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_14 (A B : Prop) : ((A → B) → B → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_15 (A : Prop) : ((A → A) → A → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_16 (A B C D : Prop) : ((A → B) → C → D → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_17 (A B C : Prop) : ((A → B) → A → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_18 (A B C : Prop) : ((A → B) → C → A → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_19 (A B C : Prop) : ((A → A) → B → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_20 (A B C : Prop) : ((A → B) → B → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_21 (A B : Prop) : ((A → A) → A → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_22 (A B : Prop) : ((A → B) → B → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_23 (A B C : Prop) : ((A → B) → C → B → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_24 (A B : Prop) : ((A → B) → A → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_25 (A B : Prop) : ((A → A) → B → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_26 (A B C : Prop) : ((A → B) → C → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_27 (A B : Prop) : ((A → B) → A → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_13_28 (A B C : Prop) : ((A → B) → A → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_1 (A B C D : Prop) : (A → B → C → D → D) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_2 (A B C : Prop) : (A → B → C → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_3 (A B C : Prop) : (A → B → A → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_4 (A B C : Prop) : (A → A → B → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_5 (A B C : Prop) : (A → B → C → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_6 (A B : Prop) : (A → A → B → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_7 (A B : Prop) : (A → B → A → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_8 (A B C : Prop) : (A → B → B → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_9 (A B : Prop) : (A → B → B → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_10 (A B : Prop) : (A → A → A → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_11 (A B C : Prop) : (A → B → C → C → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_12 (A B : Prop) : (A → B → A → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_13 (A B : Prop) : (A → A → B → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_14 (A B : Prop) : (A → B → B → B → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_15 (A : Prop) : (A → A → A → A → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_16 (A B C D : Prop) : (A → B → C → D → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_17 (A B C : Prop) : (A → B → A → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_18 (A B C : Prop) : (A → B → C → A → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_19 (A B C : Prop) : (A → A → B → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_20 (A B C : Prop) : (A → B → B → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_21 (A B : Prop) : (A → A → A → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_22 (A B : Prop) : (A → B → B → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_23 (A B C : Prop) : (A → B → C → B → C) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_24 (A B : Prop) : (A → B → A → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_25 (A B : Prop) : (A → A → B → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_26 (A B C D : Prop) : (A → B → C → D → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_27 (A B C : Prop) : (A → A → B → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_28 (A B C : Prop) : (A → B → C → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_29 (A B C : Prop) : (A → B → A → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_30 (A B C : Prop) : (A → B → C → C → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_31 (A B : Prop) : (A → A → B → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_32 (A B : Prop) : (A → B → A → A → B) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_33 (A B C D : Prop) : (A → B → C → D → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_34 (A B C : Prop) : (A → B → C → B → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_35 (A B C : Prop) : (A → B → B → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_36 (A B C : Prop) : (A → B → C → C → A) := by
  run_tac intro_all_then_assumption
theorem propfmls_4_14_37 (A B : Prop) : (A → B → B → B → A) := by
  run_tac intro_all_then_assumption
