import Lean
open Lean Meta Elab Tactic

/- Third attempt.
When prompted to correct the tactic in order to account for the errors below, it
uses the explaination that formulas of the form ((P→C)→C)⇒C((P→C)→C)⇒C is not intuitionistically valid.
This is the case in general but not when P is true. The model fails to reason by
checking the conditions under which the formula is intuitionistic and when it is not and check
these conditions.
-/

/-- Introduce all arrows/foralls; then
    (1) try to close by using one of the freshly introduced locals exactly;
    (2) otherwise, try one-step function locals: apply `h : X → tgt`,
        then close the single subgoal `⊢ X` using another introduced local. -/
elab "intro_all_then_assumption" : tactic => do
  let g0 ← getMainGoal
  let (fs, g) ← g0.intros               -- `fs : Array FVarId` (new locals), `g : MVarId`
  replaceMainGoal [g]
  withMainContext do
    let locals : Array Expr := fs.map mkFVar
    let tgt ← g.getType

    -- (1) exact match
    for e in locals do
      if (← isDefEq (← inferType e) tgt) then
        g.assign e
        replaceMainGoal []
        return

    -- (2) one-step functional case: h : X → tgt
    for h in locals do
      let ty ← inferType h
      match ty with
      | Expr.forallE _ _ _ _ =>
          -- Try `apply h`; if it doesn't fit, skip.
          try
            let subs ← g.apply h   -- should produce exactly one subgoal: ⊢ X
            match subs with
            | [sg] =>
                let need ← sg.getType
                -- close ⊢ X with one of the introduced locals
                for e in locals do
                  if (← isDefEq (← inferType e) need) then
                    sg.assign e
                    replaceMainGoal []
                    return
                -- if we couldn’t close X, undo and try another `h`
                -- (we just keep looping)
            | _ => pure ()         -- ignore weird arities
          catch _ => pure ()
      | _ => pure ()

    throwError "intro_all_then_assumption: no introduced hypothesis matches the goal"

theorem t1 (A B : Prop) : A → B → A := by intro_all_then_assumption
theorem t2 (A B : Prop) : A → B → B := by intro_all_then_assumption
theorem t3 (A : Prop)   : A → A → A := by intro_all_then_assumption
theorem propfmls_3_4_4 (A B : Prop) : ((A → B) → B → B) := by intro_all_then_assumption
theorem propfmls_3_4_5 (A : Prop) : ((A → A) → A → A) := by intro_all_then_assumption
theorem propfmls_3_4_6 (A B : Prop) : ((A → B) → A → B) := by intro_all_then_assumption
theorem propfmls_3_5_1 (A B C : Prop) : (A → B → C → C) := by intro_all_then_assumption
theorem propfmls_3_5_2 (A B : Prop) : (A → B → A → A) := by intro_all_then_assumption
theorem propfmls_3_5_3 (A B : Prop) : (A → A → B → B) := by intro_all_then_assumption
theorem propfmls_3_5_4 (A B : Prop) : (A → B → B → B) := by intro_all_then_assumption
theorem propfmls_3_5_5 (A : Prop) : (A → A → A → A) := by intro_all_then_assumption
theorem propfmls_3_5_6 (A B C : Prop) : (A → B → C → B) := by intro_all_then_assumption
theorem propfmls_3_5_7 (A B : Prop) : (A → A → B → A) := by intro_all_then_assumption
theorem propfmls_3_5_8 (A B : Prop) : (A → B → A → B) := by intro_all_then_assumption
theorem propfmls_3_5_9 (A B C : Prop) : (A → B → C → A) := by intro_all_then_assumption
theorem propfmls_3_5_10 (A B : Prop) : (A → B → B → A) := by intro_all_then_assumption

theorem propfmls_4_2_1 (A B C : Prop) : (((A → B → B) → C) → C) := by intro_all_then_assumption
theorem propfmls_4_2_2 (A B : Prop) : (((A → B → B) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_2_3 (A B : Prop) : (((A → A → A) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_2_4 (A B : Prop) : (((A → B → B) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_2_5 (A : Prop) : (((A → A → A) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_2_6 (A B C : Prop) : (((A → B → A) → C) → C) := by intro_all_then_assumption
theorem propfmls_4_2_7 (A B : Prop) : (((A → B → A) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_2_8 (A B : Prop) : (((A → B → A) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_1 (A B C D : Prop) : (A → ((B → C) → D) → A) := by intro_all_then_assumption
theorem propfmls_4_4_2 (A B C : Prop) : (A → ((A → B) → C) → A) := by intro_all_then_assumption
theorem propfmls_4_4_3 (A B C : Prop) : (A → ((B → C) → B) → A) := by intro_all_then_assumption
theorem propfmls_4_4_4 (A B C : Prop) : (A → ((B → B) → C) → A) := by intro_all_then_assumption
theorem propfmls_4_4_5 (A B C : Prop) : (A → ((B → A) → C) → A) := by intro_all_then_assumption
theorem propfmls_4_4_6 (A B : Prop) : (A → ((A → A) → B) → A) := by intro_all_then_assumption
theorem propfmls_4_4_7 (A B : Prop) : (A → ((B → A) → B) → A) := by intro_all_then_assumption
theorem propfmls_4_4_8 (A B C : Prop) : (A → ((B → C) → C) → A) := by intro_all_then_assumption
theorem propfmls_4_4_9 (A B : Prop) : (A → ((A → B) → B) → A) := by intro_all_then_assumption
theorem propfmls_4_4_10 (A B : Prop) : (A → ((B → B) → B) → A) := by intro_all_then_assumption
theorem propfmls_4_4_11 (A B C : Prop) : (A → ((B → C) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_12 (A B : Prop) : (A → ((A → B) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_13 (A B : Prop) : (A → ((B → B) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_14 (A B : Prop) : (A → ((B → A) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_15 (A : Prop) : (A → ((A → A) → A) → A) := by intro_all_then_assumption
theorem propfmls_4_4_16 (A B C : Prop) : (A → ((B → A) → C) → C) := by intro_all_then_assumption
theorem propfmls_4_4_17 (A B : Prop) : (A → ((B → A) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_4_18 (A B : Prop) : (A → ((A → A) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_4_19 (A B C : Prop) : (A → ((B → B) → C) → C) := by intro_all_then_assumption
theorem propfmls_4_4_20 (A B : Prop) : (A → ((B → B) → B) → B) := by intro_all_then_assumption
theorem propfmls_4_7_1 (A B C D : Prop) : (A → (B → C → D) → A) := by intro_all_then_assumption
theorem propfmls_4_7_2 (A B C : Prop) : (A → (A → B → C) → A) := by intro_all_then_assumption
theorem propfmls_4_7_3 (A B C : Prop) : (A → (B → C → B) → A) := by intro_all_then_assumption
theorem propfmls_4_7_4 (A B C : Prop) : (A → (B → B → C) → A) := by intro_all_then_assumption
theorem propfmls_4_7_5 (A B C : Prop) : (A → (B → A → C) → A) := by intro_all_then_assumption
theorem propfmls_4_7_6 (A B : Prop) : (A → (A → A → B) → A) := by intro_all_then_assumption
theorem propfmls_4_7_7 (A B : Prop) : (A → (B → A → B) → A) := by intro_all_then_assumption
theorem propfmls_4_7_8 (A B C : Prop) : (A → (B → C → C) → A) := by intro_all_then_assumption
theorem propfmls_4_7_9 (A B : Prop) : (A → (A → B → B) → A) := by intro_all_then_assumption
theorem propfmls_4_7_10 (A B : Prop) : (A → (B → B → B) → A) := by intro_all_then_assumption
theorem propfmls_4_7_11 (A B C : Prop) : (A → (B → C → A) → A) := by intro_all_then_assumption
theorem propfmls_4_7_12 (A B : Prop) : (A → (A → B → A) → A) := by intro_all_then_assumption
theorem propfmls_4_7_13 (A B : Prop) : (A → (B → B → A) → A) := by intro_all_then_assumption
theorem propfmls_4_7_14 (A B : Prop) : (A → (B → A → A) → A) := by intro_all_then_assumption
theorem propfmls_4_7_15 (A : Prop) : (A → (A → A → A) → A) := by intro_all_then_assumption
theorem propfmls_4_7_16 (A B : Prop) : (A → (A → A → B) → B) := by intro_all_then_assumption
theorem propfmls_4_9_1 (A B C D : Prop) : (A → B → (C → D) → B) := by intro_all_then_assumption
theorem propfmls_4_9_2 (A B C : Prop) : (A → A → (B → C) → A) := by intro_all_then_assumption
theorem propfmls_4_9_3 (A B C : Prop) : (A → B → (C → A) → B) := by intro_all_then_assumption
theorem propfmls_4_9_4 (A B C : Prop) : (A → B → (A → C) → B) := by intro_all_then_assumption
theorem propfmls_4_9_5 (A B C : Prop) : (A → B → (B → C) → B) := by intro_all_then_assumption
theorem propfmls_4_9_6 (A B : Prop) : (A → A → (A → B) → A) := by intro_all_then_assumption
theorem propfmls_4_9_7 (A B : Prop) : (A → B → (B → A) → B) := by intro_all_then_assumption
theorem propfmls_4_9_8 (A B C : Prop) : (A → B → (C → C) → B) := by intro_all_then_assumption
theorem propfmls_4_9_9 (A B : Prop) : (A → A → (B → B) → A) := by intro_all_then_assumption
theorem propfmls_4_9_10 (A B : Prop) : (A → B → (A → A) → B) := by intro_all_then_assumption
theorem propfmls_4_9_11 (A B C : Prop) : (A → B → (C → B) → B) := by intro_all_then_assumption
theorem propfmls_4_9_12 (A B : Prop) : (A → A → (B → A) → A) := by intro_all_then_assumption
theorem propfmls_4_9_13 (A B : Prop) : (A → B → (A → B) → B) := by intro_all_then_assumption
theorem propfmls_4_9_14 (A B : Prop) : (A → B → (B → B) → B) := by intro_all_then_assumption
theorem propfmls_4_9_15 (A : Prop) : (A → A → (A → A) → A) := by intro_all_then_assumption
theorem propfmls_4_9_16 (A B C D : Prop) : (A → B → (C → D) → A) := by intro_all_then_assumption
theorem propfmls_4_9_17 (A B C : Prop) : (A → B → (C → B) → A) := by intro_all_then_assumption
theorem propfmls_4_9_18 (A B C : Prop) : (A → B → (B → C) → A) := by intro_all_then_assumption
theorem propfmls_4_9_19 (A B C : Prop) : (A → B → (A → C) → A) := by intro_all_then_assumption
theorem propfmls_4_9_20 (A B : Prop) : (A → B → (A → B) → A) := by intro_all_then_assumption
theorem propfmls_4_9_21 (A B C : Prop) : (A → B → (C → C) → A) := by intro_all_then_assumption
theorem propfmls_4_9_22 (A B : Prop) : (A → B → (B → B) → A) := by intro_all_then_assumption
theorem propfmls_4_9_23 (A B C : Prop) : (A → B → (C → A) → A) := by intro_all_then_assumption
theorem propfmls_4_9_24 (A B : Prop) : (A → B → (B → A) → A) := by intro_all_then_assumption
theorem propfmls_4_9_25 (A B : Prop) : (A → B → (A → A) → A) := by intro_all_then_assumption
theorem propfmls_4_9_26 (A B C : Prop) : (A → B → (B → C) → C) := by intro_all_then_assumption
theorem propfmls_4_9_27 (A B : Prop) : (A → A → (A → B) → B) := by intro_all_then_assumption
theorem propfmls_4_9_28 (A B C : Prop) : (A → B → (A → C) → C) := by intro_all_then_assumption
theorem propfmls_4_10_1 (A B C D : Prop) : (((A → B) → C) → D → D) := by intro_all_then_assumption
theorem propfmls_4_10_2 (A B C : Prop) : (((A → B) → C) → A → A) := by intro_all_then_assumption
theorem propfmls_4_10_3 (A B C : Prop) : (((A → B) → A) → C → C) := by intro_all_then_assumption
theorem propfmls_4_10_4 (A B C : Prop) : (((A → A) → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_10_5 (A B C : Prop) : (((A → B) → C) → B → B) := by intro_all_then_assumption
theorem propfmls_4_10_6 (A B : Prop) : (((A → A) → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_10_7 (A B : Prop) : (((A → B) → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_10_8 (A B C : Prop) : (((A → B) → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_10_9 (A B : Prop) : (((A → B) → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_10_10 (A B : Prop) : (((A → A) → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_10_11 (A B C : Prop) : (((A → B) → C) → C → C) := by intro_all_then_assumption
theorem propfmls_4_10_12 (A B : Prop) : (((A → B) → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_10_13 (A B : Prop) : (((A → A) → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_10_14 (A B : Prop) : (((A → B) → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_10_15 (A : Prop) : (((A → A) → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_10_16 (A B C : Prop) : (((A → B) → C) → B → C) := by intro_all_then_assumption
theorem propfmls_4_10_17 (A B : Prop) : (((A → B) → A) → B → A) := by intro_all_then_assumption
theorem propfmls_4_10_18 (A B : Prop) : (((A → A) → B) → A → B) := by intro_all_then_assumption
theorem propfmls_4_10_19 (A B C : Prop) : (((A → A) → B) → C → B) := by intro_all_then_assumption
theorem propfmls_4_10_20 (A B : Prop) : (((A → A) → A) → B → A) := by intro_all_then_assumption
theorem propfmls_4_11_1 (A B C D : Prop) : ((A → B → C) → D → D) := by intro_all_then_assumption
theorem propfmls_4_11_2 (A B C : Prop) : ((A → B → C) → A → A) := by intro_all_then_assumption
theorem propfmls_4_11_3 (A B C : Prop) : ((A → B → A) → C → C) := by intro_all_then_assumption
theorem propfmls_4_11_4 (A B C : Prop) : ((A → A → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_11_5 (A B C : Prop) : ((A → B → C) → B → B) := by intro_all_then_assumption
theorem propfmls_4_11_6 (A B : Prop) : ((A → A → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_11_7 (A B : Prop) : ((A → B → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_11_8 (A B C : Prop) : ((A → B → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_11_9 (A B : Prop) : ((A → B → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_11_10 (A B : Prop) : ((A → A → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_11_11 (A B C : Prop) : ((A → B → C) → C → C) := by intro_all_then_assumption
theorem propfmls_4_11_12 (A B : Prop) : ((A → B → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_11_13 (A B : Prop) : ((A → A → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_11_14 (A B : Prop) : ((A → B → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_11_15 (A : Prop) : ((A → A → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_11_16 (A B : Prop) : ((A → A → B) → A → B) := by intro_all_then_assumption
theorem propfmls_4_12_1 (A B C D : Prop) : (A → (B → C) → D → D) := by intro_all_then_assumption
theorem propfmls_4_12_2 (A B C : Prop) : (A → (B → C) → A → A) := by intro_all_then_assumption
theorem propfmls_4_12_3 (A B C : Prop) : (A → (B → A) → C → C) := by intro_all_then_assumption
theorem propfmls_4_12_4 (A B C : Prop) : (A → (A → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_12_5 (A B C : Prop) : (A → (B → C) → B → B) := by intro_all_then_assumption
theorem propfmls_4_12_6 (A B : Prop) : (A → (A → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_12_7 (A B : Prop) : (A → (B → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_12_8 (A B C : Prop) : (A → (B → B) → C → C) := by intro_all_then_assumption
theorem propfmls_4_12_9 (A B : Prop) : (A → (B → B) → A → A) := by intro_all_then_assumption
theorem propfmls_4_12_10 (A B : Prop) : (A → (A → A) → B → B) := by intro_all_then_assumption
theorem propfmls_4_12_11 (A B C : Prop) : (A → (B → C) → C → C) := by intro_all_then_assumption
theorem propfmls_4_12_12 (A B : Prop) : (A → (B → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_12_13 (A B : Prop) : (A → (A → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_12_14 (A B : Prop) : (A → (B → B) → B → B) := by intro_all_then_assumption
theorem propfmls_4_12_15 (A : Prop) : (A → (A → A) → A → A) := by intro_all_then_assumption
theorem propfmls_4_12_16 (A B C D : Prop) : (A → (B → C) → D → A) := by intro_all_then_assumption
theorem propfmls_4_12_17 (A B C : Prop) : (A → (A → B) → C → A) := by intro_all_then_assumption
theorem propfmls_4_12_18 (A B C : Prop) : (A → (B → C) → B → A) := by intro_all_then_assumption
theorem propfmls_4_12_19 (A B C : Prop) : (A → (B → B) → C → A) := by intro_all_then_assumption
theorem propfmls_4_12_20 (A B C : Prop) : (A → (B → A) → C → A) := by intro_all_then_assumption
theorem propfmls_4_12_21 (A B : Prop) : (A → (A → A) → B → A) := by intro_all_then_assumption
theorem propfmls_4_12_22 (A B : Prop) : (A → (B → A) → B → A) := by intro_all_then_assumption
theorem propfmls_4_12_23 (A B C : Prop) : (A → (B → C) → C → A) := by intro_all_then_assumption
theorem propfmls_4_12_24 (A B : Prop) : (A → (A → B) → B → A) := by intro_all_then_assumption
theorem propfmls_4_12_25 (A B : Prop) : (A → (B → B) → B → A) := by intro_all_then_assumption
theorem propfmls_4_12_26 (A B C : Prop) : (A → (B → C) → B → C) := by intro_all_then_assumption
theorem propfmls_4_12_27 (A B : Prop) : (A → (A → B) → A → B) := by intro_all_then_assumption
theorem propfmls_4_12_28 (A B C : Prop) : (A → (A → B) → C → B) := by intro_all_then_assumption
theorem propfmls_4_13_1 (A B C D : Prop) : ((A → B) → C → D → D) := by intro_all_then_assumption
theorem propfmls_4_13_2 (A B C : Prop) : ((A → B) → C → A → A) := by intro_all_then_assumption
theorem propfmls_4_13_3 (A B C : Prop) : ((A → B) → A → C → C) := by intro_all_then_assumption
theorem propfmls_4_13_4 (A B C : Prop) : ((A → A) → B → C → C) := by intro_all_then_assumption
theorem propfmls_4_13_5 (A B C : Prop) : ((A → B) → C → B → B) := by intro_all_then_assumption
theorem propfmls_4_13_6 (A B : Prop) : ((A → A) → B → A → A) := by intro_all_then_assumption
theorem propfmls_4_13_7 (A B : Prop) : ((A → B) → A → B → B) := by intro_all_then_assumption
theorem propfmls_4_13_8 (A B C : Prop) : ((A → B) → B → C → C) := by intro_all_then_assumption
theorem propfmls_4_13_9 (A B : Prop) : ((A → B) → B → A → A) := by intro_all_then_assumption
theorem propfmls_4_13_10 (A B : Prop) : ((A → A) → A → B → B) := by intro_all_then_assumption
theorem propfmls_4_13_11 (A B C : Prop) : ((A → B) → C → C → C) := by intro_all_then_assumption
theorem propfmls_4_13_12 (A B : Prop) : ((A → B) → A → A → A) := by intro_all_then_assumption
theorem propfmls_4_13_13 (A B : Prop) : ((A → A) → B → B → B) := by intro_all_then_assumption
theorem propfmls_4_13_14 (A B : Prop) : ((A → B) → B → B → B) := by intro_all_then_assumption
theorem propfmls_4_13_15 (A : Prop) : ((A → A) → A → A → A) := by intro_all_then_assumption
theorem propfmls_4_13_16 (A B C D : Prop) : ((A → B) → C → D → C) := by intro_all_then_assumption
theorem propfmls_4_13_17 (A B C : Prop) : ((A → B) → A → C → A) := by intro_all_then_assumption
theorem propfmls_4_13_18 (A B C : Prop) : ((A → B) → C → A → C) := by intro_all_then_assumption
theorem propfmls_4_13_19 (A B C : Prop) : ((A → A) → B → C → B) := by intro_all_then_assumption
theorem propfmls_4_13_20 (A B C : Prop) : ((A → B) → B → C → B) := by intro_all_then_assumption
theorem propfmls_4_13_21 (A B : Prop) : ((A → A) → A → B → A) := by intro_all_then_assumption
theorem propfmls_4_13_22 (A B : Prop) : ((A → B) → B → A → B) := by intro_all_then_assumption
theorem propfmls_4_13_23 (A B C : Prop) : ((A → B) → C → B → C) := by intro_all_then_assumption
theorem propfmls_4_13_24 (A B : Prop) : ((A → B) → A → B → A) := by intro_all_then_assumption
theorem propfmls_4_13_25 (A B : Prop) : ((A → A) → B → A → B) := by intro_all_then_assumption
theorem propfmls_4_13_26 (A B C : Prop) : ((A → B) → C → A → B) := by intro_all_then_assumption
theorem propfmls_4_13_27 (A B : Prop) : ((A → B) → A → A → B) := by intro_all_then_assumption
theorem propfmls_4_13_28 (A B C : Prop) : ((A → B) → A → C → B) := by intro_all_then_assumption
theorem propfmls_4_14_1 (A B C D : Prop) : (A → B → C → D → D) := by intro_all_then_assumption
theorem propfmls_4_14_2 (A B C : Prop) : (A → B → C → A → A) := by intro_all_then_assumption
theorem propfmls_4_14_3 (A B C : Prop) : (A → B → A → C → C) := by intro_all_then_assumption
theorem propfmls_4_14_4 (A B C : Prop) : (A → A → B → C → C) := by intro_all_then_assumption
theorem propfmls_4_14_5 (A B C : Prop) : (A → B → C → B → B) := by intro_all_then_assumption
theorem propfmls_4_14_6 (A B : Prop) : (A → A → B → A → A) := by intro_all_then_assumption
theorem propfmls_4_14_7 (A B : Prop) : (A → B → A → B → B) := by intro_all_then_assumption
theorem propfmls_4_14_8 (A B C : Prop) : (A → B → B → C → C) := by intro_all_then_assumption
theorem propfmls_4_14_9 (A B : Prop) : (A → B → B → A → A) := by intro_all_then_assumption
theorem propfmls_4_14_10 (A B : Prop) : (A → A → A → B → B) := by intro_all_then_assumption
theorem propfmls_4_14_11 (A B C : Prop) : (A → B → C → C → C) := by intro_all_then_assumption
theorem propfmls_4_14_12 (A B : Prop) : (A → B → A → A → A) := by intro_all_then_assumption
theorem propfmls_4_14_13 (A B : Prop) : (A → A → B → B → B) := by intro_all_then_assumption
theorem propfmls_4_14_14 (A B : Prop) : (A → B → B → B → B) := by intro_all_then_assumption
theorem propfmls_4_14_15 (A : Prop) : (A → A → A → A → A) := by intro_all_then_assumption
theorem propfmls_4_14_16 (A B C D : Prop) : (A → B → C → D → C) := by intro_all_then_assumption
theorem propfmls_4_14_17 (A B C : Prop) : (A → B → A → C → A) := by intro_all_then_assumption
theorem propfmls_4_14_18 (A B C : Prop) : (A → B → C → A → C) := by intro_all_then_assumption
theorem propfmls_4_14_19 (A B C : Prop) : (A → A → B → C → B) := by intro_all_then_assumption
theorem propfmls_4_14_20 (A B C : Prop) : (A → B → B → C → B) := by intro_all_then_assumption
theorem propfmls_4_14_21 (A B : Prop) : (A → A → A → B → A) := by intro_all_then_assumption
theorem propfmls_4_14_22 (A B : Prop) : (A → B → B → A → B) := by intro_all_then_assumption
theorem propfmls_4_14_23 (A B C : Prop) : (A → B → C → B → C) := by intro_all_then_assumption
theorem propfmls_4_14_24 (A B : Prop) : (A → B → A → B → A) := by intro_all_then_assumption
theorem propfmls_4_14_25 (A B : Prop) : (A → A → B → A → B) := by intro_all_then_assumption
theorem propfmls_4_14_26 (A B C D : Prop) : (A → B → C → D → B) := by intro_all_then_assumption
theorem propfmls_4_14_27 (A B C : Prop) : (A → A → B → C → A) := by intro_all_then_assumption
theorem propfmls_4_14_28 (A B C : Prop) : (A → B → C → A → B) := by intro_all_then_assumption
theorem propfmls_4_14_29 (A B C : Prop) : (A → B → A → C → B) := by intro_all_then_assumption
theorem propfmls_4_14_30 (A B C : Prop) : (A → B → C → C → B) := by intro_all_then_assumption
theorem propfmls_4_14_31 (A B : Prop) : (A → A → B → B → A) := by intro_all_then_assumption
theorem propfmls_4_14_32 (A B : Prop) : (A → B → A → A → B) := by intro_all_then_assumption
theorem propfmls_4_14_33 (A B C D : Prop) : (A → B → C → D → A) := by intro_all_then_assumption
theorem propfmls_4_14_34 (A B C : Prop) : (A → B → C → B → A) := by intro_all_then_assumption
theorem propfmls_4_14_35 (A B C : Prop) : (A → B → B → C → A) := by intro_all_then_assumption
theorem propfmls_4_14_36 (A B C : Prop) : (A → B → C → C → A) := by intro_all_then_assumption
theorem propfmls_4_14_37 (A B : Prop) : (A → B → B → B → A) := by intro_all_then_assumption
