import Lean

open Lean Meta Elab Tactic

/-
  Prompt: I want you to write a tactic in lean which can prove uniformly
  tautologies obtained by adding well formed parentheses to a
  series of implications. Things of the form (((A → B → B) → C) → C)
  for instance. You MUST use "run_tac" so that the proof of any statement is
  as follows. theorem propfmls_4_2_1 (A B C : Prop) :
  (((A → B → B) → C) → C) := by run_tac tactic_name What
  you need to define is tactic_name. You must only use meta programming
  and not advanced mathlib functionalities. Please write the whole lean
  file with some examples as described.
-/

/- Note: first attempt leads to recursion problem. Feedback with error report.-/


/-
  A very small proof-search tactic for implicational tautologies.

  It works on goals built only from `→` (i.e. Π / ∀ in `Prop`) by:

  * repeatedly introducing arrows (`intro`);
  * closing the goal by an existing hypothesis when possible;
  * otherwise, trying to `apply` any hypothesis whose result matches the goal,
    and recursively solving the generated subgoals.

  This is enough to uniformly handle things like
    (((A → B → B) → C) → C)
  and many other parenthesised implication tautologies.
-/

/-- Recursive worker: tries to solve the given goal using only →-intro and →-elim. -/
partial def solveImp (g : MVarId) : TacticM Unit := do
  g.withContext do
    let tgt ← g.getType
    -- 1. If the goal is a function / implication, introduce an argument.
    match tgt with
    | Expr.forallE _ _ _ _ =>
        let (_, g') ← g.intro1
        solveImp g'
    | _ =>
      -- 2. Try to close the goal directly from the context (by assumption).
      let lctx ← getLCtx
      for decl in lctx do
        if !decl.isImplementationDetail then
          let h := Expr.fvar decl.fvarId
          let hTy ← inferType h
          if (← isDefEq tgt hTy) then
            g.assign h
            return

      -- 3. Otherwise, try to `apply` any hypothesis, and solve the subgoals.
      let lctx2 ← getLCtx
      for decl in lctx2 do
        if !decl.isImplementationDetail then
          let h := Expr.fvar decl.fvarId
          try
            let subgoals ← g.apply h
            for sg in subgoals do
              solveImp sg
            return
          catch _ =>
            pure ()

      -- If we reach here, we failed to solve the goal.
      throwError "tactic_name: could not solve goal {tgt}."

/-- Tactic entry point to be used via `run_tac tactic_name`. -/
def tactic_name : TacticM Unit := do
  let g ← getMainGoal
  solveImp g
  -- all goals should be solved now
  setGoals []


/-! ### Examples -/

theorem t1 (A B : Prop) : A → B → A := by
  run_tac tactic_name
theorem t2 (A B : Prop) : A → B → B := by
  run_tac tactic_name
theorem t3 (A : Prop)   : A → A → A := by
  run_tac tactic_name
theorem propfmls_3_1_1 (A B : Prop) : (((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_3_1_2 (A : Prop) : (((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_3_3_1 (A B C : Prop) : (A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_3_3_2 (A B : Prop) : (A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_3_3_3 (A B : Prop) : (A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_3_4_4 (A B : Prop) : ((A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_3_4_5 (A : Prop) : ((A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_3_4_6 (A B : Prop) : ((A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_3_5_1 (A B C : Prop) : (A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_3_5_2 (A B : Prop) : (A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_3_5_3 (A B : Prop) : (A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_3_5_4 (A B : Prop) : (A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_3_5_5 (A : Prop) : (A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_3_5_6 (A B C : Prop) : (A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_3_5_7 (A B : Prop) : (A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_3_5_8 (A B : Prop) : (A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_3_5_9 (A B C : Prop) : (A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_3_5_10 (A B : Prop) : (A → B → B → A) := by
  run_tac tactic_name

theorem propfmls_4_2_1 (A B C : Prop) : (((A → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_2_2 (A B : Prop) : (((A → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_2_3 (A B : Prop) : (((A → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_2_4 (A B : Prop) : (((A → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_2_5 (A : Prop) : (((A → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_2_6 (A B C : Prop) : (((A → B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_2_7 (A B : Prop) : (((A → B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_2_8 (A B : Prop) : (((A → B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_1 (A B C D : Prop) : (A → ((B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_2 (A B C : Prop) : (A → ((A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_3 (A B C : Prop) : (A → ((B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_4 (A B C : Prop) : (A → ((B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_5 (A B C : Prop) : (A → ((B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_6 (A B : Prop) : (A → ((A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_7 (A B : Prop) : (A → ((B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_8 (A B C : Prop) : (A → ((B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_9 (A B : Prop) : (A → ((A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_10 (A B : Prop) : (A → ((B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_11 (A B C : Prop) : (A → ((B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_12 (A B : Prop) : (A → ((A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_13 (A B : Prop) : (A → ((B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_14 (A B : Prop) : (A → ((B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_15 (A : Prop) : (A → ((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_4_16 (A B C : Prop) : (A → ((B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_4_17 (A B : Prop) : (A → ((B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_4_18 (A B : Prop) : (A → ((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_4_19 (A B C : Prop) : (A → ((B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_4_20 (A B : Prop) : (A → ((B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_7_1 (A B C D : Prop) : (A → (B → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_2 (A B C : Prop) : (A → (A → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_3 (A B C : Prop) : (A → (B → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_4 (A B C : Prop) : (A → (B → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_5 (A B C : Prop) : (A → (B → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_6 (A B : Prop) : (A → (A → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_7 (A B : Prop) : (A → (B → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_8 (A B C : Prop) : (A → (B → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_9 (A B : Prop) : (A → (A → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_10 (A B : Prop) : (A → (B → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_11 (A B C : Prop) : (A → (B → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_12 (A B : Prop) : (A → (A → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_13 (A B : Prop) : (A → (B → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_14 (A B : Prop) : (A → (B → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_15 (A : Prop) : (A → (A → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_7_16 (A B : Prop) : (A → (A → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_1 (A B C D : Prop) : (A → B → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_2 (A B C : Prop) : (A → A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_3 (A B C : Prop) : (A → B → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_4 (A B C : Prop) : (A → B → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_5 (A B C : Prop) : (A → B → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_6 (A B : Prop) : (A → A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_7 (A B : Prop) : (A → B → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_8 (A B C : Prop) : (A → B → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_9 (A B : Prop) : (A → A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_10 (A B : Prop) : (A → B → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_11 (A B C : Prop) : (A → B → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_12 (A B : Prop) : (A → A → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_13 (A B : Prop) : (A → B → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_14 (A B : Prop) : (A → B → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_15 (A : Prop) : (A → A → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_16 (A B C D : Prop) : (A → B → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_17 (A B C : Prop) : (A → B → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_18 (A B C : Prop) : (A → B → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_19 (A B C : Prop) : (A → B → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_20 (A B : Prop) : (A → B → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_21 (A B C : Prop) : (A → B → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_22 (A B : Prop) : (A → B → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_23 (A B C : Prop) : (A → B → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_24 (A B : Prop) : (A → B → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_25 (A B : Prop) : (A → B → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_4_9_26 (A B C : Prop) : (A → B → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_9_27 (A B : Prop) : (A → A → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_4_9_28 (A B C : Prop) : (A → B → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_4_10_1 (A B C D : Prop) : (((A → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_4_10_2 (A B C : Prop) : (((A → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_10_3 (A B C : Prop) : (((A → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_10_4 (A B C : Prop) : (((A → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_10_5 (A B C : Prop) : (((A → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_10_6 (A B : Prop) : (((A → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_10_7 (A B : Prop) : (((A → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_10_8 (A B C : Prop) : (((A → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_10_9 (A B : Prop) : (((A → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_10_10 (A B : Prop) : (((A → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_10_11 (A B C : Prop) : (((A → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_10_12 (A B : Prop) : (((A → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_10_13 (A B : Prop) : (((A → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_10_14 (A B : Prop) : (((A → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_10_15 (A : Prop) : (((A → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_10_16 (A B C : Prop) : (((A → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_4_10_17 (A B : Prop) : (((A → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_10_18 (A B : Prop) : (((A → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_4_10_19 (A B C : Prop) : (((A → A) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_4_10_20 (A B : Prop) : (((A → A) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_11_1 (A B C D : Prop) : ((A → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_4_11_2 (A B C : Prop) : ((A → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_11_3 (A B C : Prop) : ((A → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_11_4 (A B C : Prop) : ((A → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_11_5 (A B C : Prop) : ((A → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_11_6 (A B : Prop) : ((A → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_11_7 (A B : Prop) : ((A → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_11_8 (A B C : Prop) : ((A → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_11_9 (A B : Prop) : ((A → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_11_10 (A B : Prop) : ((A → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_11_11 (A B C : Prop) : ((A → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_11_12 (A B : Prop) : ((A → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_11_13 (A B : Prop) : ((A → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_11_14 (A B : Prop) : ((A → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_11_15 (A : Prop) : ((A → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_11_16 (A B : Prop) : ((A → A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_4_12_1 (A B C D : Prop) : (A → (B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_4_12_2 (A B C : Prop) : (A → (B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_12_3 (A B C : Prop) : (A → (B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_12_4 (A B C : Prop) : (A → (A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_12_5 (A B C : Prop) : (A → (B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_12_6 (A B : Prop) : (A → (A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_12_7 (A B : Prop) : (A → (B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_12_8 (A B C : Prop) : (A → (B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_12_9 (A B : Prop) : (A → (B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_12_10 (A B : Prop) : (A → (A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_12_11 (A B C : Prop) : (A → (B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_4_12_12 (A B : Prop) : (A → (B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_12_13 (A B : Prop) : (A → (A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_12_14 (A B : Prop) : (A → (B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_4_12_15 (A : Prop) : (A → (A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_4_12_16 (A B C D : Prop) : (A → (B → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_4_12_17 (A B C : Prop) : (A → (A → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_4_12_18 (A B C : Prop) : (A → (B → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_12_19 (A B C : Prop) : (A → (B → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_4_12_20 (A B C : Prop) : (A → (B → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_4_12_21 (A B : Prop) : (A → (A → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_12_22 (A B : Prop) : (A → (B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_12_23 (A B C : Prop) : (A → (B → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_4_12_24 (A B : Prop) : (A → (A → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_12_25 (A B : Prop) : (A → (B → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_4_12_26 (A B C : Prop) : (A → (B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_4_12_27 (A B : Prop) : (A → (A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_4_12_28 (A B C : Prop) : (A → (A → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_4_13_1 (A B C D : Prop) : ((A → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_4_13_2 (A B C : Prop) : ((A → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_4_13_3 (A B C : Prop) : ((A → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_4_13_4 (A B C : Prop) : ((A → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_4_13_5 (A B C : Prop) : ((A → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_4_13_6 (A B : Prop) : ((A → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_4_13_7 (A B : Prop) : ((A → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_4_13_8 (A B C : Prop) : ((A → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_4_13_9 (A B : Prop) : ((A → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_4_13_10 (A B : Prop) : ((A → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_4_13_11 (A B C : Prop) : ((A → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_4_13_12 (A B : Prop) : ((A → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_4_13_13 (A B : Prop) : ((A → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_4_13_14 (A B : Prop) : ((A → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_4_13_15 (A : Prop) : ((A → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_4_13_16 (A B C D : Prop) : ((A → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_4_13_17 (A B C : Prop) : ((A → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_4_13_18 (A B C : Prop) : ((A → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_4_13_19 (A B C : Prop) : ((A → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_4_13_20 (A B C : Prop) : ((A → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_4_13_21 (A B : Prop) : ((A → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_4_13_22 (A B : Prop) : ((A → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_4_13_23 (A B C : Prop) : ((A → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_4_13_24 (A B : Prop) : ((A → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_4_13_25 (A B : Prop) : ((A → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_4_13_26 (A B C : Prop) : ((A → B) → C → A → B) := by
  run_tac tactic_name
theorem propfmls_4_13_27 (A B : Prop) : ((A → B) → A → A → B) := by
  run_tac tactic_name
theorem propfmls_4_13_28 (A B C : Prop) : ((A → B) → A → C → B) := by
  run_tac tactic_name
theorem propfmls_4_14_1 (A B C D : Prop) : (A → B → C → D → D) := by
  run_tac tactic_name
theorem propfmls_4_14_2 (A B C : Prop) : (A → B → C → A → A) := by
  run_tac tactic_name
theorem propfmls_4_14_3 (A B C : Prop) : (A → B → A → C → C) := by
  run_tac tactic_name
theorem propfmls_4_14_4 (A B C : Prop) : (A → A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_4_14_5 (A B C : Prop) : (A → B → C → B → B) := by
  run_tac tactic_name
theorem propfmls_4_14_6 (A B : Prop) : (A → A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_4_14_7 (A B : Prop) : (A → B → A → B → B) := by
  run_tac tactic_name
theorem propfmls_4_14_8 (A B C : Prop) : (A → B → B → C → C) := by
  run_tac tactic_name
theorem propfmls_4_14_9 (A B : Prop) : (A → B → B → A → A) := by
  run_tac tactic_name
theorem propfmls_4_14_10 (A B : Prop) : (A → A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_4_14_11 (A B C : Prop) : (A → B → C → C → C) := by
  run_tac tactic_name
theorem propfmls_4_14_12 (A B : Prop) : (A → B → A → A → A) := by
  run_tac tactic_name
theorem propfmls_4_14_13 (A B : Prop) : (A → A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_4_14_14 (A B : Prop) : (A → B → B → B → B) := by
  run_tac tactic_name
theorem propfmls_4_14_15 (A : Prop) : (A → A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_4_14_16 (A B C D : Prop) : (A → B → C → D → C) := by
  run_tac tactic_name
theorem propfmls_4_14_17 (A B C : Prop) : (A → B → A → C → A) := by
  run_tac tactic_name
theorem propfmls_4_14_18 (A B C : Prop) : (A → B → C → A → C) := by
  run_tac tactic_name
theorem propfmls_4_14_19 (A B C : Prop) : (A → A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_4_14_20 (A B C : Prop) : (A → B → B → C → B) := by
  run_tac tactic_name
theorem propfmls_4_14_21 (A B : Prop) : (A → A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_4_14_22 (A B : Prop) : (A → B → B → A → B) := by
  run_tac tactic_name
theorem propfmls_4_14_23 (A B C : Prop) : (A → B → C → B → C) := by
  run_tac tactic_name
theorem propfmls_4_14_24 (A B : Prop) : (A → B → A → B → A) := by
  run_tac tactic_name
theorem propfmls_4_14_25 (A B : Prop) : (A → A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_4_14_26 (A B C D : Prop) : (A → B → C → D → B) := by
  run_tac tactic_name
theorem propfmls_4_14_27 (A B C : Prop) : (A → A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_4_14_28 (A B C : Prop) : (A → B → C → A → B) := by
  run_tac tactic_name
theorem propfmls_4_14_29 (A B C : Prop) : (A → B → A → C → B) := by
  run_tac tactic_name
theorem propfmls_4_14_30 (A B C : Prop) : (A → B → C → C → B) := by
  run_tac tactic_name
theorem propfmls_4_14_31 (A B : Prop) : (A → A → B → B → A) := by
  run_tac tactic_name
theorem propfmls_4_14_32 (A B : Prop) : (A → B → A → A → B) := by
  run_tac tactic_name
theorem propfmls_4_14_33 (A B C D : Prop) : (A → B → C → D → A) := by
  run_tac tactic_name
theorem propfmls_4_14_34 (A B C : Prop) : (A → B → C → B → A) := by
  run_tac tactic_name
theorem propfmls_4_14_35 (A B C : Prop) : (A → B → B → C → A) := by
  run_tac tactic_name
theorem propfmls_4_14_36 (A B C : Prop) : (A → B → C → C → A) := by
  run_tac tactic_name
theorem propfmls_4_14_37 (A B : Prop) : (A → B → B → B → A) := by
  run_tac tactic_name

theorem propfmls_5_1_1 (A B C : Prop) : (((((A → A) → B) → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_1_2 (A B : Prop) : (((((A → A) → B) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_1_3 (A B : Prop) : (((((A → A) → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_1_4 (A B : Prop) : (((((A → A) → B) → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_1_5 (A : Prop) : (((((A → A) → A) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_1_6 (A B : Prop) : (((((A → B) → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_1 (A B C D : Prop) : (((A → (B → C) → A) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_3_2 (A B C : Prop) : (((A → (B → C) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_3 (A B C : Prop) : (((A → (A → B) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_3_4 (A B C : Prop) : (((A → (B → B) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_3_5 (A B C : Prop) : (((A → (B → C) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_3_6 (A B : Prop) : (((A → (B → B) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_7 (A B : Prop) : (((A → (A → B) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_8 (A B C : Prop) : (((A → (B → A) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_3_9 (A B : Prop) : (((A → (B → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_10 (A B : Prop) : (((A → (A → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_3_11 (A B C : Prop) : (((A → (B → C) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_12 (A B : Prop) : (((A → (A → B) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_13 (A B : Prop) : (((A → (B → B) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_14 (A B : Prop) : (((A → (B → A) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_15 (A : Prop) : (((A → (A → A) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_16 (A B C : Prop) : (((A → (A → B) → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_3_17 (A B : Prop) : (((A → (A → B) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_3_18 (A B : Prop) : (((A → (A → B) → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_1 (A B C D E : Prop) : (A → (((B → C) → D) → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_2 (A B C D : Prop) : (A → (((A → B) → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_3 (A B C D : Prop) : (A → (((B → C) → D) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_4 (A B C D : Prop) : (A → (((B → C) → B) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_5 (A B C D : Prop) : (A → (((B → B) → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_6 (A B C D : Prop) : (A → (((B → A) → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_7 (A B C : Prop) : (A → (((A → A) → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_8 (A B C : Prop) : (A → (((B → A) → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_9 (A B C : Prop) : (A → (((B → A) → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_10 (A B C D : Prop) : (A → (((B → C) → D) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_11 (A B C : Prop) : (A → (((A → B) → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_12 (A B C : Prop) : (A → (((B → B) → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_13 (A B C : Prop) : (A → (((B → C) → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_14 (A B C D : Prop) : (A → (((B → C) → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_15 (A B C : Prop) : (A → (((A → B) → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_16 (A B C : Prop) : (A → (((B → C) → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_17 (A B C : Prop) : (A → (((B → B) → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_18 (A B C D : Prop) : (A → (((B → C) → A) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_19 (A B C : Prop) : (A → (((A → B) → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_20 (A B C : Prop) : (A → (((B → C) → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_21 (A B C : Prop) : (A → (((B → B) → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_22 (A B C : Prop) : (A → (((B → A) → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_23 (A B : Prop) : (A → (((A → A) → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_24 (A B : Prop) : (A → (((B → A) → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_25 (A B C : Prop) : (A → (((B → C) → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_26 (A B : Prop) : (A → (((A → B) → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_27 (A B : Prop) : (A → (((B → B) → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_28 (A B C D : Prop) : (A → (((B → C) → D) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_29 (A B C : Prop) : (A → (((A → B) → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_30 (A B C : Prop) : (A → (((B → C) → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_31 (A B C : Prop) : (A → (((B → B) → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_32 (A B C : Prop) : (A → (((B → A) → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_33 (A B : Prop) : (A → (((A → A) → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_34 (A B : Prop) : (A → (((B → A) → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_35 (A B C : Prop) : (A → (((B → C) → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_36 (A B : Prop) : (A → (((A → B) → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_37 (A B : Prop) : (A → (((B → B) → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_38 (A B C D : Prop) : (A → (((B → C) → D) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_39 (A B C : Prop) : (A → (((A → B) → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_40 (A B C : Prop) : (A → (((B → C) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_41 (A B C : Prop) : (A → (((B → B) → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_42 (A B C : Prop) : (A → (((B → A) → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_43 (A B : Prop) : (A → (((A → A) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_44 (A B : Prop) : (A → (((B → A) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_45 (A B C : Prop) : (A → (((B → C) → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_46 (A B : Prop) : (A → (((A → B) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_47 (A B : Prop) : (A → (((B → B) → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_48 (A B C : Prop) : (A → (((B → C) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_49 (A B : Prop) : (A → (((A → B) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_50 (A B : Prop) : (A → (((B → B) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_51 (A B : Prop) : (A → (((B → A) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_52 (A : Prop) : (A → (((A → A) → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_5_53 (A B C D : Prop) : (A → (((B → C) → A) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_5_54 (A B C : Prop) : (A → (((B → C) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_55 (A B C : Prop) : (A → (((A → B) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_5_56 (A B C : Prop) : (A → (((B → B) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_5_57 (A B C : Prop) : (A → (((B → C) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_5_58 (A B : Prop) : (A → (((B → B) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_59 (A B : Prop) : (A → (((A → B) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_60 (A B C : Prop) : (A → (((B → A) → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_5_61 (A B : Prop) : (A → (((B → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_62 (A B : Prop) : (A → (((A → A) → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_5_63 (A B C : Prop) : (A → (((A → B) → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_5_64 (A B : Prop) : (A → (((A → B) → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_1 (A B C D : Prop) : ((((A → B) → C → C) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_6_2 (A B C : Prop) : ((((A → B) → C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_3 (A B C : Prop) : ((((A → B) → A → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_6_4 (A B C : Prop) : ((((A → A) → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_6_5 (A B C : Prop) : ((((A → B) → C → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_6 (A B : Prop) : ((((A → A) → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_7 (A B : Prop) : ((((A → B) → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_8 (A B C : Prop) : ((((A → B) → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_6_9 (A B : Prop) : ((((A → B) → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_10 (A B : Prop) : ((((A → A) → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_11 (A B C : Prop) : ((((A → B) → C → C) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_6_12 (A B : Prop) : ((((A → B) → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_13 (A B : Prop) : ((((A → A) → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_14 (A B : Prop) : ((((A → B) → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_6_15 (A : Prop) : ((((A → A) → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_16 (A B C : Prop) : ((((A → B) → A → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_6_17 (A B : Prop) : ((((A → B) → A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_6_18 (A B : Prop) : ((((A → B) → A → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_1 (A B C D : Prop) : (((A → B → C → C) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_7_2 (A B C : Prop) : (((A → B → C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_3 (A B C : Prop) : (((A → B → A → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_4 (A B C : Prop) : (((A → A → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_5 (A B C : Prop) : (((A → B → C → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_6 (A B : Prop) : (((A → A → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_7 (A B : Prop) : (((A → B → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_8 (A B C : Prop) : (((A → B → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_9 (A B : Prop) : (((A → B → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_10 (A B : Prop) : (((A → A → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_11 (A B C : Prop) : (((A → B → C → C) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_12 (A B : Prop) : (((A → B → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_13 (A B : Prop) : (((A → A → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_14 (A B : Prop) : (((A → B → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_15 (A : Prop) : (((A → A → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_16 (A B C D : Prop) : (((A → B → C → B) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_7_17 (A B C : Prop) : (((A → B → C → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_18 (A B C : Prop) : (((A → A → B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_19 (A B C : Prop) : (((A → B → A → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_20 (A B C : Prop) : (((A → B → C → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_21 (A B : Prop) : (((A → B → A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_22 (A B : Prop) : (((A → A → B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_23 (A B C : Prop) : (((A → B → C → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_24 (A B : Prop) : (((A → A → B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_25 (A B : Prop) : (((A → B → A → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_26 (A B C D : Prop) : (((A → B → C → A) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_7_27 (A B C : Prop) : (((A → B → C → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_28 (A B C : Prop) : (((A → B → B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_29 (A B C : Prop) : (((A → B → C → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_7_30 (A B : Prop) : (((A → B → B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_7_31 (A B C : Prop) : (((A → B → C → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_7_32 (A B : Prop) : (((A → B → B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_1 (A B C D E : Prop) : (A → ((B → C → D) → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_2 (A B C D : Prop) : (A → ((A → B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_3 (A B C D : Prop) : (A → ((B → C → D) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_4 (A B C D : Prop) : (A → ((B → C → B) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_5 (A B C D : Prop) : (A → ((B → B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_6 (A B C D : Prop) : (A → ((B → A → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_7 (A B C : Prop) : (A → ((A → A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_8 (A B C : Prop) : (A → ((B → A → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_9 (A B C : Prop) : (A → ((B → A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_10 (A B C D : Prop) : (A → ((B → C → D) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_11 (A B C : Prop) : (A → ((A → B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_12 (A B C : Prop) : (A → ((B → B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_13 (A B C : Prop) : (A → ((B → C → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_14 (A B C D : Prop) : (A → ((B → C → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_15 (A B C : Prop) : (A → ((A → B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_16 (A B C : Prop) : (A → ((B → C → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_17 (A B C : Prop) : (A → ((B → B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_18 (A B C D : Prop) : (A → ((B → C → A) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_19 (A B C : Prop) : (A → ((A → B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_20 (A B C : Prop) : (A → ((B → C → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_21 (A B C : Prop) : (A → ((B → B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_22 (A B C : Prop) : (A → ((B → A → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_23 (A B : Prop) : (A → ((A → A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_24 (A B : Prop) : (A → ((B → A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_25 (A B C : Prop) : (A → ((B → C → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_26 (A B : Prop) : (A → ((A → B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_27 (A B : Prop) : (A → ((B → B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_28 (A B C D : Prop) : (A → ((B → C → D) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_29 (A B C : Prop) : (A → ((A → B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_30 (A B C : Prop) : (A → ((B → C → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_31 (A B C : Prop) : (A → ((B → B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_32 (A B C : Prop) : (A → ((B → A → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_33 (A B : Prop) : (A → ((A → A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_34 (A B : Prop) : (A → ((B → A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_35 (A B C : Prop) : (A → ((B → C → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_36 (A B : Prop) : (A → ((A → B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_37 (A B : Prop) : (A → ((B → B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_38 (A B C D : Prop) : (A → ((B → C → D) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_39 (A B C : Prop) : (A → ((A → B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_40 (A B C : Prop) : (A → ((B → C → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_41 (A B C : Prop) : (A → ((B → B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_42 (A B C : Prop) : (A → ((B → A → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_43 (A B : Prop) : (A → ((A → A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_44 (A B : Prop) : (A → ((B → A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_45 (A B C : Prop) : (A → ((B → C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_46 (A B : Prop) : (A → ((A → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_47 (A B : Prop) : (A → ((B → B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_48 (A B C : Prop) : (A → ((B → C → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_49 (A B : Prop) : (A → ((A → B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_50 (A B : Prop) : (A → ((B → B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_51 (A B : Prop) : (A → ((B → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_52 (A : Prop) : (A → ((A → A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_9_53 (A B C D : Prop) : (A → ((B → C → A) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_9_54 (A B C : Prop) : (A → ((B → C → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_55 (A B C : Prop) : (A → ((A → B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_56 (A B C : Prop) : (A → ((B → B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_57 (A B C : Prop) : (A → ((B → C → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_58 (A B : Prop) : (A → ((B → B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_59 (A B : Prop) : (A → ((A → B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_60 (A B C : Prop) : (A → ((B → A → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_61 (A B : Prop) : (A → ((B → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_62 (A B : Prop) : (A → ((A → A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_63 (A B C D : Prop) : (A → ((B → C → C) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_9_64 (A B C : Prop) : (A → ((A → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_65 (A B C : Prop) : (A → ((B → C → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_66 (A B C : Prop) : (A → ((B → B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_67 (A B C : Prop) : (A → ((B → C → C) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_68 (A B : Prop) : (A → ((A → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_69 (A B : Prop) : (A → ((B → B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_70 (A B C D : Prop) : (A → ((B → C → B) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_9_71 (A B C : Prop) : (A → ((B → A → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_72 (A B C : Prop) : (A → ((B → C → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_9_73 (A B C : Prop) : (A → ((B → C → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_9_74 (A B : Prop) : (A → ((B → A → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_10_1 (A B C : Prop) : (((A → A) → (B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_10_2 (A B : Prop) : (((A → A) → (B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_10_3 (A B : Prop) : (((A → A) → (A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_10_4 (A B : Prop) : (((A → A) → (B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_10_5 (A : Prop) : (((A → A) → (A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_1 (A B C D E : Prop) : (A → (B → (C → D) → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_2 (A B C D : Prop) : (A → (A → (B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_3 (A B C D : Prop) : (A → (B → (C → D) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_4 (A B C D : Prop) : (A → (B → (C → B) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_5 (A B C D : Prop) : (A → (B → (B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_6 (A B C D : Prop) : (A → (B → (A → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_7 (A B C : Prop) : (A → (A → (A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_8 (A B C : Prop) : (A → (B → (A → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_9 (A B C : Prop) : (A → (B → (A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_10 (A B C D : Prop) : (A → (B → (C → D) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_11 (A B C : Prop) : (A → (A → (B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_12 (A B C : Prop) : (A → (B → (B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_13 (A B C : Prop) : (A → (B → (C → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_14 (A B C D : Prop) : (A → (B → (C → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_15 (A B C : Prop) : (A → (A → (B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_16 (A B C : Prop) : (A → (B → (C → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_17 (A B C : Prop) : (A → (B → (B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_18 (A B C D : Prop) : (A → (B → (C → A) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_19 (A B C : Prop) : (A → (A → (B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_20 (A B C : Prop) : (A → (B → (C → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_21 (A B C : Prop) : (A → (B → (B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_22 (A B C : Prop) : (A → (B → (A → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_23 (A B : Prop) : (A → (A → (A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_24 (A B : Prop) : (A → (B → (A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_25 (A B C : Prop) : (A → (B → (C → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_26 (A B : Prop) : (A → (A → (B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_27 (A B : Prop) : (A → (B → (B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_28 (A B C D : Prop) : (A → (B → (C → D) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_29 (A B C : Prop) : (A → (A → (B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_30 (A B C : Prop) : (A → (B → (C → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_31 (A B C : Prop) : (A → (B → (B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_32 (A B C : Prop) : (A → (B → (A → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_33 (A B : Prop) : (A → (A → (A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_34 (A B : Prop) : (A → (B → (A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_35 (A B C : Prop) : (A → (B → (C → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_36 (A B : Prop) : (A → (A → (B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_37 (A B : Prop) : (A → (B → (B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_38 (A B C D : Prop) : (A → (B → (C → D) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_39 (A B C : Prop) : (A → (A → (B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_40 (A B C : Prop) : (A → (B → (C → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_41 (A B C : Prop) : (A → (B → (B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_42 (A B C : Prop) : (A → (B → (A → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_43 (A B : Prop) : (A → (A → (A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_44 (A B : Prop) : (A → (B → (A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_45 (A B C : Prop) : (A → (B → (C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_46 (A B : Prop) : (A → (A → (B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_47 (A B : Prop) : (A → (B → (B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_48 (A B C : Prop) : (A → (B → (C → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_49 (A B : Prop) : (A → (A → (B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_50 (A B : Prop) : (A → (B → (B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_51 (A B : Prop) : (A → (B → (A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_52 (A : Prop) : (A → (A → (A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_12_53 (A B C : Prop) : (A → (A → (B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_12_54 (A B : Prop) : (A → (A → (B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_12_55 (A B : Prop) : (A → (A → (A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_12_56 (A B C : Prop) : (A → (A → (B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_12_57 (A B : Prop) : (A → (A → (B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_1 (A B C D : Prop) : ((A → B) → ((C → C) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_13_2 (A B C : Prop) : ((A → B) → ((C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_3 (A B C : Prop) : ((A → B) → ((A → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_13_4 (A B C : Prop) : ((A → A) → ((B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_13_5 (A B C : Prop) : ((A → B) → ((C → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_6 (A B : Prop) : ((A → A) → ((B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_7 (A B : Prop) : ((A → B) → ((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_8 (A B C : Prop) : ((A → B) → ((B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_13_9 (A B : Prop) : ((A → B) → ((B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_10 (A B : Prop) : ((A → A) → ((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_11 (A B C : Prop) : ((A → B) → ((C → C) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_13_12 (A B : Prop) : ((A → B) → ((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_13 (A B : Prop) : ((A → A) → ((B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_14 (A B : Prop) : ((A → B) → ((B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_15 (A : Prop) : ((A → A) → ((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_16 (A B C : Prop) : ((A → B) → ((A → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_13_17 (A B : Prop) : ((A → B) → ((A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_13_18 (A B : Prop) : ((A → B) → ((A → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_19 (A B C : Prop) : ((A → B) → ((C → C) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_20 (A B : Prop) : ((A → B) → ((B → B) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_21 (A B : Prop) : ((A → B) → ((A → A) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_13_22 (A B : Prop) : ((A → B) → ((A → B) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_1 (A B C D E : Prop) : (A → B → ((C → D) → E) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_2 (A B C D : Prop) : (A → A → ((B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_3 (A B C D : Prop) : (A → B → ((C → D) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_4 (A B C D : Prop) : (A → B → ((C → A) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_5 (A B C D : Prop) : (A → B → ((A → C) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_6 (A B C D : Prop) : (A → B → ((B → C) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_7 (A B C : Prop) : (A → A → ((A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_8 (A B C : Prop) : (A → B → ((B → C) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_9 (A B C : Prop) : (A → B → ((B → A) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_10 (A B C D : Prop) : (A → B → ((C → D) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_11 (A B C : Prop) : (A → A → ((B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_12 (A B C : Prop) : (A → B → ((A → C) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_13 (A B C : Prop) : (A → B → ((C → A) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_14 (A B C D : Prop) : (A → B → ((C → C) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_15 (A B C : Prop) : (A → A → ((B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_16 (A B C : Prop) : (A → B → ((C → C) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_17 (A B C : Prop) : (A → B → ((A → A) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_18 (A B C D : Prop) : (A → B → ((C → B) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_19 (A B C : Prop) : (A → A → ((B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_20 (A B C : Prop) : (A → B → ((C → B) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_21 (A B C : Prop) : (A → B → ((A → B) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_22 (A B C : Prop) : (A → B → ((B → B) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_23 (A B : Prop) : (A → A → ((A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_24 (A B : Prop) : (A → B → ((B → B) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_25 (A B C : Prop) : (A → B → ((C → B) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_26 (A B : Prop) : (A → A → ((B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_27 (A B : Prop) : (A → B → ((A → B) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_28 (A B C D : Prop) : (A → B → ((C → D) → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_29 (A B C : Prop) : (A → A → ((B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_30 (A B C : Prop) : (A → B → ((C → A) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_31 (A B C : Prop) : (A → B → ((A → C) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_32 (A B C : Prop) : (A → B → ((B → C) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_33 (A B : Prop) : (A → A → ((A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_34 (A B : Prop) : (A → B → ((B → A) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_35 (A B C : Prop) : (A → B → ((C → C) → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_36 (A B : Prop) : (A → A → ((B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_37 (A B : Prop) : (A → B → ((A → A) → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_38 (A B C D : Prop) : (A → B → ((C → D) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_39 (A B C : Prop) : (A → A → ((B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_40 (A B C : Prop) : (A → B → ((C → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_41 (A B C : Prop) : (A → B → ((A → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_42 (A B C : Prop) : (A → B → ((B → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_43 (A B : Prop) : (A → A → ((A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_44 (A B : Prop) : (A → B → ((B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_45 (A B C : Prop) : (A → B → ((C → C) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_46 (A B : Prop) : (A → A → ((B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_47 (A B : Prop) : (A → B → ((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_48 (A B C : Prop) : (A → B → ((C → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_49 (A B : Prop) : (A → A → ((B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_50 (A B : Prop) : (A → B → ((A → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_51 (A B : Prop) : (A → B → ((B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_52 (A : Prop) : (A → A → ((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_53 (A B C D E : Prop) : (A → B → ((C → D) → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_54 (A B C D : Prop) : (A → B → ((C → D) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_55 (A B C D : Prop) : (A → B → ((C → B) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_56 (A B C D : Prop) : (A → B → ((B → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_57 (A B C D : Prop) : (A → B → ((A → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_58 (A B C : Prop) : (A → B → ((A → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_59 (A B C : Prop) : (A → B → ((A → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_60 (A B C D : Prop) : (A → B → ((C → D) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_61 (A B C : Prop) : (A → B → ((B → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_62 (A B C : Prop) : (A → B → ((C → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_63 (A B C D : Prop) : (A → B → ((C → C) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_64 (A B C : Prop) : (A → B → ((C → C) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_65 (A B C : Prop) : (A → B → ((B → B) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_66 (A B C D : Prop) : (A → B → ((C → A) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_67 (A B C : Prop) : (A → B → ((C → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_68 (A B C : Prop) : (A → B → ((B → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_69 (A B C : Prop) : (A → B → ((A → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_70 (A B : Prop) : (A → B → ((A → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_71 (A B C : Prop) : (A → B → ((C → A) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_72 (A B : Prop) : (A → B → ((B → A) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_73 (A B C D : Prop) : (A → B → ((C → D) → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_74 (A B C : Prop) : (A → B → ((C → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_75 (A B C : Prop) : (A → B → ((B → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_76 (A B C : Prop) : (A → B → ((A → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_77 (A B : Prop) : (A → B → ((A → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_78 (A B C : Prop) : (A → B → ((C → C) → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_79 (A B : Prop) : (A → B → ((B → B) → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_80 (A B C D : Prop) : (A → B → ((C → D) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_81 (A B C : Prop) : (A → B → ((C → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_82 (A B C : Prop) : (A → B → ((B → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_83 (A B C : Prop) : (A → B → ((A → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_84 (A B : Prop) : (A → B → ((A → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_85 (A B C : Prop) : (A → B → ((C → C) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_86 (A B : Prop) : (A → B → ((B → B) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_87 (A B C : Prop) : (A → B → ((C → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_88 (A B : Prop) : (A → B → ((B → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_89 (A B : Prop) : (A → B → ((A → A) → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_14_90 (A B C D : Prop) : (A → B → ((C → B) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_14_91 (A B C : Prop) : (A → A → ((B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_92 (A B C : Prop) : (A → B → ((A → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_93 (A B C : Prop) : (A → B → ((C → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_94 (A B : Prop) : (A → A → ((B → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_95 (A B C : Prop) : (A → B → ((B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_96 (A B : Prop) : (A → A → ((A → A) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_14_97 (A B C D : Prop) : (A → B → ((C → A) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_14_98 (A B C : Prop) : (A → B → ((B → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_99 (A B C : Prop) : (A → B → ((C → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_100 (A B C : Prop) : (A → B → ((A → A) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_101 (A B C D : Prop) : (A → B → ((C → C) → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_14_102 (A B C : Prop) : (A → A → ((B → B) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_103 (A B C : Prop) : (A → B → ((C → C) → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_14_104 (A B : Prop) : (A → A → ((B → B) → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_18_1 (A B C D E : Prop) : (A → ((B → C) → D → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_2 (A B C D : Prop) : (A → ((A → B) → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_3 (A B C D : Prop) : (A → ((B → C) → D → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_4 (A B C D : Prop) : (A → ((B → C) → B → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_5 (A B C D : Prop) : (A → ((B → B) → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_6 (A B C D : Prop) : (A → ((B → A) → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_7 (A B C : Prop) : (A → ((A → A) → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_8 (A B C : Prop) : (A → ((B → A) → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_9 (A B C : Prop) : (A → ((B → A) → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_10 (A B C D : Prop) : (A → ((B → C) → D → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_11 (A B C : Prop) : (A → ((A → B) → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_12 (A B C : Prop) : (A → ((B → B) → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_13 (A B C : Prop) : (A → ((B → C) → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_14 (A B C D : Prop) : (A → ((B → C) → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_15 (A B C : Prop) : (A → ((A → B) → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_16 (A B C : Prop) : (A → ((B → C) → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_17 (A B C : Prop) : (A → ((B → B) → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_18 (A B C D : Prop) : (A → ((B → C) → A → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_19 (A B C : Prop) : (A → ((A → B) → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_20 (A B C : Prop) : (A → ((B → C) → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_21 (A B C : Prop) : (A → ((B → B) → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_22 (A B C : Prop) : (A → ((B → A) → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_23 (A B : Prop) : (A → ((A → A) → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_24 (A B : Prop) : (A → ((B → A) → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_25 (A B C : Prop) : (A → ((B → C) → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_26 (A B : Prop) : (A → ((A → B) → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_27 (A B : Prop) : (A → ((B → B) → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_28 (A B C D : Prop) : (A → ((B → C) → D → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_29 (A B C : Prop) : (A → ((A → B) → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_30 (A B C : Prop) : (A → ((B → C) → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_31 (A B C : Prop) : (A → ((B → B) → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_32 (A B C : Prop) : (A → ((B → A) → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_33 (A B : Prop) : (A → ((A → A) → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_34 (A B : Prop) : (A → ((B → A) → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_35 (A B C : Prop) : (A → ((B → C) → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_36 (A B : Prop) : (A → ((A → B) → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_37 (A B : Prop) : (A → ((B → B) → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_38 (A B C D : Prop) : (A → ((B → C) → D → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_39 (A B C : Prop) : (A → ((A → B) → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_40 (A B C : Prop) : (A → ((B → C) → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_41 (A B C : Prop) : (A → ((B → B) → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_42 (A B C : Prop) : (A → ((B → A) → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_43 (A B : Prop) : (A → ((A → A) → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_44 (A B : Prop) : (A → ((B → A) → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_45 (A B C : Prop) : (A → ((B → C) → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_46 (A B : Prop) : (A → ((A → B) → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_47 (A B : Prop) : (A → ((B → B) → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_48 (A B C : Prop) : (A → ((B → C) → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_49 (A B : Prop) : (A → ((A → B) → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_50 (A B : Prop) : (A → ((B → B) → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_51 (A B : Prop) : (A → ((B → A) → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_52 (A : Prop) : (A → ((A → A) → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_18_53 (A B C : Prop) : (A → ((B → A) → A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_18_54 (A B : Prop) : (A → ((B → A) → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_18_55 (A B : Prop) : (A → ((A → A) → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_18_56 (A B C : Prop) : (A → ((B → B) → A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_18_57 (A B : Prop) : (A → ((B → B) → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_21_1 (A B C D E : Prop) : (A → (B → C → D → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_2 (A B C D : Prop) : (A → (A → B → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_3 (A B C D : Prop) : (A → (B → C → D → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_4 (A B C D : Prop) : (A → (B → C → B → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_5 (A B C D : Prop) : (A → (B → B → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_6 (A B C D : Prop) : (A → (B → A → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_7 (A B C : Prop) : (A → (A → A → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_8 (A B C : Prop) : (A → (B → A → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_9 (A B C : Prop) : (A → (B → A → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_10 (A B C D : Prop) : (A → (B → C → D → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_11 (A B C : Prop) : (A → (A → B → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_12 (A B C : Prop) : (A → (B → B → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_13 (A B C : Prop) : (A → (B → C → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_14 (A B C D : Prop) : (A → (B → C → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_15 (A B C : Prop) : (A → (A → B → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_16 (A B C : Prop) : (A → (B → C → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_17 (A B C : Prop) : (A → (B → B → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_18 (A B C D : Prop) : (A → (B → C → A → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_19 (A B C : Prop) : (A → (A → B → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_20 (A B C : Prop) : (A → (B → C → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_21 (A B C : Prop) : (A → (B → B → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_22 (A B C : Prop) : (A → (B → A → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_23 (A B : Prop) : (A → (A → A → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_24 (A B : Prop) : (A → (B → A → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_25 (A B C : Prop) : (A → (B → C → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_26 (A B : Prop) : (A → (A → B → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_27 (A B : Prop) : (A → (B → B → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_28 (A B C D : Prop) : (A → (B → C → D → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_29 (A B C : Prop) : (A → (A → B → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_30 (A B C : Prop) : (A → (B → C → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_31 (A B C : Prop) : (A → (B → B → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_32 (A B C : Prop) : (A → (B → A → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_33 (A B : Prop) : (A → (A → A → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_34 (A B : Prop) : (A → (B → A → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_35 (A B C : Prop) : (A → (B → C → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_36 (A B : Prop) : (A → (A → B → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_37 (A B : Prop) : (A → (B → B → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_38 (A B C D : Prop) : (A → (B → C → D → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_39 (A B C : Prop) : (A → (A → B → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_40 (A B C : Prop) : (A → (B → C → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_41 (A B C : Prop) : (A → (B → B → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_42 (A B C : Prop) : (A → (B → A → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_43 (A B : Prop) : (A → (A → A → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_44 (A B : Prop) : (A → (B → A → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_45 (A B C : Prop) : (A → (B → C → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_46 (A B : Prop) : (A → (A → B → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_47 (A B : Prop) : (A → (B → B → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_48 (A B C : Prop) : (A → (B → C → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_49 (A B : Prop) : (A → (A → B → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_50 (A B : Prop) : (A → (B → B → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_51 (A B : Prop) : (A → (B → A → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_52 (A : Prop) : (A → (A → A → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_21_53 (A B : Prop) : (A → (A → A → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_1 (A B C D E : Prop) : (A → B → (C → D → E) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_2 (A B C D : Prop) : (A → A → (B → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_3 (A B C D : Prop) : (A → B → (C → D → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_4 (A B C D : Prop) : (A → B → (C → A → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_5 (A B C D : Prop) : (A → B → (A → C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_6 (A B C D : Prop) : (A → B → (B → C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_7 (A B C : Prop) : (A → A → (A → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_8 (A B C : Prop) : (A → B → (B → C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_9 (A B C : Prop) : (A → B → (B → A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_10 (A B C D : Prop) : (A → B → (C → D → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_11 (A B C : Prop) : (A → A → (B → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_12 (A B C : Prop) : (A → B → (A → C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_13 (A B C : Prop) : (A → B → (C → A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_14 (A B C D : Prop) : (A → B → (C → C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_15 (A B C : Prop) : (A → A → (B → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_16 (A B C : Prop) : (A → B → (C → C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_17 (A B C : Prop) : (A → B → (A → A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_18 (A B C D : Prop) : (A → B → (C → B → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_19 (A B C : Prop) : (A → A → (B → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_20 (A B C : Prop) : (A → B → (C → B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_21 (A B C : Prop) : (A → B → (A → B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_22 (A B C : Prop) : (A → B → (B → B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_23 (A B : Prop) : (A → A → (A → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_24 (A B : Prop) : (A → B → (B → B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_25 (A B C : Prop) : (A → B → (C → B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_26 (A B : Prop) : (A → A → (B → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_27 (A B : Prop) : (A → B → (A → B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_28 (A B C D : Prop) : (A → B → (C → D → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_29 (A B C : Prop) : (A → A → (B → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_30 (A B C : Prop) : (A → B → (C → A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_31 (A B C : Prop) : (A → B → (A → C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_32 (A B C : Prop) : (A → B → (B → C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_33 (A B : Prop) : (A → A → (A → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_34 (A B : Prop) : (A → B → (B → A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_35 (A B C : Prop) : (A → B → (C → C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_36 (A B : Prop) : (A → A → (B → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_37 (A B : Prop) : (A → B → (A → A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_38 (A B C D : Prop) : (A → B → (C → D → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_39 (A B C : Prop) : (A → A → (B → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_40 (A B C : Prop) : (A → B → (C → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_41 (A B C : Prop) : (A → B → (A → C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_42 (A B C : Prop) : (A → B → (B → C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_43 (A B : Prop) : (A → A → (A → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_44 (A B : Prop) : (A → B → (B → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_45 (A B C : Prop) : (A → B → (C → C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_46 (A B : Prop) : (A → A → (B → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_47 (A B : Prop) : (A → B → (A → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_48 (A B C : Prop) : (A → B → (C → B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_49 (A B : Prop) : (A → A → (B → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_50 (A B : Prop) : (A → B → (A → B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_51 (A B : Prop) : (A → B → (B → B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_52 (A : Prop) : (A → A → (A → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_53 (A B C D E : Prop) : (A → B → (C → D → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_54 (A B C D : Prop) : (A → B → (C → D → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_55 (A B C D : Prop) : (A → B → (C → B → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_56 (A B C D : Prop) : (A → B → (B → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_57 (A B C D : Prop) : (A → B → (A → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_58 (A B C : Prop) : (A → B → (A → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_59 (A B C : Prop) : (A → B → (A → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_60 (A B C D : Prop) : (A → B → (C → D → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_61 (A B C : Prop) : (A → B → (B → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_62 (A B C : Prop) : (A → B → (C → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_63 (A B C D : Prop) : (A → B → (C → C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_64 (A B C : Prop) : (A → B → (C → C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_65 (A B C : Prop) : (A → B → (B → B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_66 (A B C D : Prop) : (A → B → (C → A → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_67 (A B C : Prop) : (A → B → (C → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_68 (A B C : Prop) : (A → B → (B → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_69 (A B C : Prop) : (A → B → (A → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_70 (A B : Prop) : (A → B → (A → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_71 (A B C : Prop) : (A → B → (C → A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_72 (A B : Prop) : (A → B → (B → A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_73 (A B C D : Prop) : (A → B → (C → D → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_74 (A B C : Prop) : (A → B → (C → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_75 (A B C : Prop) : (A → B → (B → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_76 (A B C : Prop) : (A → B → (A → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_77 (A B : Prop) : (A → B → (A → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_78 (A B C : Prop) : (A → B → (C → C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_79 (A B : Prop) : (A → B → (B → B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_80 (A B C D : Prop) : (A → B → (C → D → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_81 (A B C : Prop) : (A → B → (C → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_82 (A B C : Prop) : (A → B → (B → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_83 (A B C : Prop) : (A → B → (A → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_84 (A B : Prop) : (A → B → (A → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_85 (A B C : Prop) : (A → B → (C → C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_86 (A B : Prop) : (A → B → (B → B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_87 (A B C : Prop) : (A → B → (C → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_88 (A B : Prop) : (A → B → (B → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_89 (A B : Prop) : (A → B → (A → A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_23_90 (A B C : Prop) : (A → B → (B → B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_23_91 (A B : Prop) : (A → A → (A → A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_23_92 (A B C : Prop) : (A → B → (A → B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_23_93 (A B C : Prop) : (A → B → (B → A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_23_94 (A B C : Prop) : (A → B → (A → A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_24_1 (A B C D : Prop) : (((A → A) → B) → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_2 (A B C : Prop) : (((A → A) → A) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_3 (A B C : Prop) : (((A → A) → B) → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_4 (A B C : Prop) : (((A → A) → B) → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_5 (A B C : Prop) : (((A → A) → B) → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_6 (A B : Prop) : (((A → A) → A) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_7 (A B : Prop) : (((A → A) → B) → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_8 (A B C : Prop) : (((A → A) → B) → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_9 (A B : Prop) : (((A → A) → A) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_10 (A B : Prop) : (((A → A) → B) → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_11 (A B C : Prop) : (((A → A) → B) → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_12 (A B : Prop) : (((A → A) → A) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_13 (A B : Prop) : (((A → A) → B) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_14 (A B : Prop) : (((A → A) → B) → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_15 (A : Prop) : (((A → A) → A) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_16 (A B C : Prop) : (((A → A) → B) → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_24_17 (A B : Prop) : (((A → A) → B) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_18 (A B : Prop) : (((A → A) → A) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_19 (A B C : Prop) : (((A → B) → C) → (A → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_24_20 (A B : Prop) : (((A → B) → A) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_24_21 (A B : Prop) : (((A → B) → B) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_24_22 (A B : Prop) : (((A → B) → A) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_1 (A B C D E : Prop) : (A → (B → C) → (D → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_2 (A B C D : Prop) : (A → (A → B) → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_3 (A B C D : Prop) : (A → (B → C) → (D → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_4 (A B C D : Prop) : (A → (B → C) → (B → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_5 (A B C D : Prop) : (A → (B → B) → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_6 (A B C D : Prop) : (A → (B → A) → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_7 (A B C : Prop) : (A → (A → A) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_8 (A B C : Prop) : (A → (B → A) → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_9 (A B C : Prop) : (A → (B → A) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_10 (A B C D : Prop) : (A → (B → C) → (D → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_11 (A B C : Prop) : (A → (A → B) → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_12 (A B C : Prop) : (A → (B → B) → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_13 (A B C : Prop) : (A → (B → C) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_14 (A B C D : Prop) : (A → (B → C) → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_15 (A B C : Prop) : (A → (A → B) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_16 (A B C : Prop) : (A → (B → C) → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_17 (A B C : Prop) : (A → (B → B) → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_18 (A B C D : Prop) : (A → (B → C) → (A → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_19 (A B C : Prop) : (A → (A → B) → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_20 (A B C : Prop) : (A → (B → C) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_21 (A B C : Prop) : (A → (B → B) → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_22 (A B C : Prop) : (A → (B → A) → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_23 (A B : Prop) : (A → (A → A) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_24 (A B : Prop) : (A → (B → A) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_25 (A B C : Prop) : (A → (B → C) → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_26 (A B : Prop) : (A → (A → B) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_27 (A B : Prop) : (A → (B → B) → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_28 (A B C D : Prop) : (A → (B → C) → (D → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_29 (A B C : Prop) : (A → (A → B) → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_30 (A B C : Prop) : (A → (B → C) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_31 (A B C : Prop) : (A → (B → B) → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_32 (A B C : Prop) : (A → (B → A) → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_33 (A B : Prop) : (A → (A → A) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_34 (A B : Prop) : (A → (B → A) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_35 (A B C : Prop) : (A → (B → C) → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_36 (A B : Prop) : (A → (A → B) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_37 (A B : Prop) : (A → (B → B) → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_38 (A B C D : Prop) : (A → (B → C) → (D → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_39 (A B C : Prop) : (A → (A → B) → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_40 (A B C : Prop) : (A → (B → C) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_41 (A B C : Prop) : (A → (B → B) → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_42 (A B C : Prop) : (A → (B → A) → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_43 (A B : Prop) : (A → (A → A) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_44 (A B : Prop) : (A → (B → A) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_45 (A B C : Prop) : (A → (B → C) → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_46 (A B : Prop) : (A → (A → B) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_47 (A B : Prop) : (A → (B → B) → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_48 (A B C : Prop) : (A → (B → C) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_49 (A B : Prop) : (A → (A → B) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_50 (A B : Prop) : (A → (B → B) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_51 (A B : Prop) : (A → (B → A) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_52 (A : Prop) : (A → (A → A) → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_26_53 (A B C D : Prop) : (A → (B → C) → (A → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_26_54 (A B C : Prop) : (A → (B → C) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_55 (A B C : Prop) : (A → (A → B) → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_26_56 (A B C : Prop) : (A → (B → B) → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_26_57 (A B C : Prop) : (A → (B → C) → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_26_58 (A B : Prop) : (A → (B → B) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_59 (A B : Prop) : (A → (A → B) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_60 (A B C : Prop) : (A → (B → A) → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_26_61 (A B : Prop) : (A → (B → A) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_62 (A B : Prop) : (A → (A → A) → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_63 (A B C D : Prop) : (A → (A → B) → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_64 (A B C : Prop) : (A → (A → B) → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_65 (A B C : Prop) : (A → (A → B) → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_66 (A B C : Prop) : (A → (A → B) → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_67 (A B : Prop) : (A → (A → B) → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_68 (A B C : Prop) : (A → (A → B) → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_69 (A B : Prop) : (A → (A → B) → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_70 (A B C : Prop) : (A → (A → B) → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_71 (A B : Prop) : (A → (A → B) → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_26_72 (A B C : Prop) : (A → (A → B) → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_26_73 (A B C : Prop) : (A → (B → C) → (A → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_1 (A B C D E : Prop) : ((A → B) → C → (D → E) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_2 (A B C D : Prop) : ((A → B) → A → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_3 (A B C D : Prop) : ((A → B) → C → (D → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_4 (A B C D : Prop) : ((A → B) → C → (A → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_5 (A B C D : Prop) : ((A → A) → B → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_6 (A B C D : Prop) : ((A → B) → B → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_7 (A B C : Prop) : ((A → A) → A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_8 (A B C : Prop) : ((A → B) → B → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_9 (A B C : Prop) : ((A → B) → B → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_10 (A B C D : Prop) : ((A → B) → C → (D → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_11 (A B C : Prop) : ((A → B) → A → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_12 (A B C : Prop) : ((A → A) → B → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_13 (A B C : Prop) : ((A → B) → C → (A → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_14 (A B C D : Prop) : ((A → B) → C → (B → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_15 (A B C : Prop) : ((A → B) → A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_16 (A B C : Prop) : ((A → B) → C → (B → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_17 (A B C : Prop) : ((A → A) → B → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_18 (A B C D : Prop) : ((A → B) → C → (C → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_19 (A B C : Prop) : ((A → B) → A → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_20 (A B C : Prop) : ((A → B) → C → (C → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_21 (A B C : Prop) : ((A → A) → B → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_22 (A B C : Prop) : ((A → B) → B → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_23 (A B : Prop) : ((A → A) → A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_24 (A B : Prop) : ((A → B) → B → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_25 (A B C : Prop) : ((A → B) → C → (C → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_26 (A B : Prop) : ((A → B) → A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_27 (A B : Prop) : ((A → A) → B → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_28 (A B C D : Prop) : ((A → B) → C → (D → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_29 (A B C : Prop) : ((A → B) → A → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_30 (A B C : Prop) : ((A → B) → C → (A → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_31 (A B C : Prop) : ((A → A) → B → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_32 (A B C : Prop) : ((A → B) → B → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_33 (A B : Prop) : ((A → A) → A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_34 (A B : Prop) : ((A → B) → B → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_35 (A B C : Prop) : ((A → B) → C → (B → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_36 (A B : Prop) : ((A → B) → A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_37 (A B : Prop) : ((A → A) → B → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_38 (A B C D : Prop) : ((A → B) → C → (D → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_39 (A B C : Prop) : ((A → B) → A → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_40 (A B C : Prop) : ((A → B) → C → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_41 (A B C : Prop) : ((A → A) → B → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_42 (A B C : Prop) : ((A → B) → B → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_43 (A B : Prop) : ((A → A) → A → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_44 (A B : Prop) : ((A → B) → B → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_45 (A B C : Prop) : ((A → B) → C → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_46 (A B : Prop) : ((A → B) → A → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_47 (A B : Prop) : ((A → A) → B → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_48 (A B C : Prop) : ((A → B) → C → (C → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_49 (A B : Prop) : ((A → B) → A → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_50 (A B : Prop) : ((A → A) → B → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_51 (A B : Prop) : ((A → B) → B → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_52 (A : Prop) : ((A → A) → A → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_53 (A B C D : Prop) : ((A → B) → C → (C → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_27_54 (A B C : Prop) : ((A → B) → C → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_55 (A B C : Prop) : ((A → B) → A → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_56 (A B C : Prop) : ((A → A) → B → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_57 (A B C : Prop) : ((A → B) → C → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_58 (A B : Prop) : ((A → A) → B → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_59 (A B : Prop) : ((A → B) → A → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_60 (A B C : Prop) : ((A → B) → B → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_61 (A B : Prop) : ((A → B) → B → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_27_62 (A B : Prop) : ((A → A) → A → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_63 (A B C D : Prop) : ((A → B) → A → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_64 (A B C : Prop) : ((A → B) → A → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_65 (A B C : Prop) : ((A → B) → A → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_66 (A B C : Prop) : ((A → B) → A → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_67 (A B : Prop) : ((A → B) → A → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_68 (A B C : Prop) : ((A → B) → A → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_69 (A B : Prop) : ((A → B) → A → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_70 (A B C : Prop) : ((A → B) → A → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_71 (A B : Prop) : ((A → B) → A → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_27_72 (A B C : Prop) : ((A → B) → A → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_27_73 (A B C : Prop) : ((A → B) → C → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_1 (A B C D E : Prop) : (A → B → C → (D → E) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_2 (A B C D : Prop) : (A → B → A → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_3 (A B C D : Prop) : (A → B → C → (D → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_4 (A B C D : Prop) : (A → B → C → (A → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_5 (A B C D : Prop) : (A → A → B → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_6 (A B C D : Prop) : (A → B → B → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_7 (A B C : Prop) : (A → A → A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_8 (A B C : Prop) : (A → B → B → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_9 (A B C : Prop) : (A → B → B → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_10 (A B C D : Prop) : (A → B → C → (D → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_11 (A B C : Prop) : (A → B → A → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_12 (A B C : Prop) : (A → A → B → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_13 (A B C : Prop) : (A → B → C → (A → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_14 (A B C D : Prop) : (A → B → C → (B → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_15 (A B C : Prop) : (A → B → A → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_16 (A B C : Prop) : (A → B → C → (B → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_17 (A B C : Prop) : (A → A → B → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_18 (A B C D : Prop) : (A → B → C → (C → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_19 (A B C : Prop) : (A → B → A → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_20 (A B C : Prop) : (A → B → C → (C → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_21 (A B C : Prop) : (A → A → B → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_22 (A B C : Prop) : (A → B → B → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_23 (A B : Prop) : (A → A → A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_24 (A B : Prop) : (A → B → B → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_25 (A B C : Prop) : (A → B → C → (C → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_26 (A B : Prop) : (A → B → A → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_27 (A B : Prop) : (A → A → B → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_28 (A B C D : Prop) : (A → B → C → (D → D) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_29 (A B C : Prop) : (A → B → A → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_30 (A B C : Prop) : (A → B → C → (A → A) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_31 (A B C : Prop) : (A → A → B → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_32 (A B C : Prop) : (A → B → B → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_33 (A B : Prop) : (A → A → A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_34 (A B : Prop) : (A → B → B → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_35 (A B C : Prop) : (A → B → C → (B → B) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_36 (A B : Prop) : (A → B → A → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_37 (A B : Prop) : (A → A → B → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_38 (A B C D : Prop) : (A → B → C → (D → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_39 (A B C : Prop) : (A → B → A → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_40 (A B C : Prop) : (A → B → C → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_41 (A B C : Prop) : (A → A → B → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_42 (A B C : Prop) : (A → B → B → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_43 (A B : Prop) : (A → A → A → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_44 (A B : Prop) : (A → B → B → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_45 (A B C : Prop) : (A → B → C → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_46 (A B : Prop) : (A → B → A → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_47 (A B : Prop) : (A → A → B → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_48 (A B C : Prop) : (A → B → C → (C → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_49 (A B : Prop) : (A → B → A → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_50 (A B : Prop) : (A → A → B → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_51 (A B : Prop) : (A → B → B → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_52 (A : Prop) : (A → A → A → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_53 (A B C D E : Prop) : (A → B → C → (D → E) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_54 (A B C D : Prop) : (A → A → B → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_55 (A B C D : Prop) : (A → B → C → (D → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_56 (A B C D : Prop) : (A → B → C → (A → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_57 (A B C D : Prop) : (A → B → A → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_58 (A B C D : Prop) : (A → B → C → (D → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_59 (A B C : Prop) : (A → A → B → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_60 (A B C : Prop) : (A → B → A → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_61 (A B C : Prop) : (A → B → C → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_62 (A B C D : Prop) : (A → B → C → (C → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_63 (A B C : Prop) : (A → A → B → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_64 (A B C : Prop) : (A → B → C → (C → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_65 (A B C : Prop) : (A → B → A → (A → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_66 (A B C D : Prop) : (A → B → C → (B → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_67 (A B C : Prop) : (A → A → B → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_68 (A B C : Prop) : (A → B → C → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_69 (A B C : Prop) : (A → B → A → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_70 (A B C : Prop) : (A → B → C → (B → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_71 (A B : Prop) : (A → A → B → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_72 (A B : Prop) : (A → B → A → (B → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_73 (A B C D : Prop) : (A → B → C → (D → D) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_74 (A B C : Prop) : (A → A → B → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_75 (A B C : Prop) : (A → B → C → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_76 (A B C : Prop) : (A → B → A → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_77 (A B C : Prop) : (A → B → C → (C → C) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_78 (A B : Prop) : (A → A → B → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_79 (A B : Prop) : (A → B → A → (A → A) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_80 (A B C D : Prop) : (A → B → C → (D → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_81 (A B C : Prop) : (A → A → B → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_82 (A B C : Prop) : (A → B → C → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_83 (A B C : Prop) : (A → B → A → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_84 (A B C : Prop) : (A → B → C → (C → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_85 (A B : Prop) : (A → A → B → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_86 (A B : Prop) : (A → B → A → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_87 (A B C : Prop) : (A → B → C → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_88 (A B : Prop) : (A → A → B → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_89 (A B : Prop) : (A → B → A → (B → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_90 (A B C D E : Prop) : (A → B → C → (D → E) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_91 (A B C D : Prop) : (A → B → C → (D → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_92 (A B C D : Prop) : (A → B → C → (B → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_93 (A B C D : Prop) : (A → B → B → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_94 (A B C D : Prop) : (A → B → C → (D → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_95 (A B C : Prop) : (A → B → B → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_96 (A B C : Prop) : (A → B → C → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_97 (A B C D : Prop) : (A → B → C → (C → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_98 (A B C : Prop) : (A → B → C → (C → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_99 (A B C : Prop) : (A → B → B → (B → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_100 (A B C D : Prop) : (A → B → C → (A → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_101 (A B C : Prop) : (A → B → C → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_102 (A B C : Prop) : (A → B → B → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_103 (A B C : Prop) : (A → B → C → (A → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_104 (A B : Prop) : (A → B → B → (A → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_105 (A B C D : Prop) : (A → B → C → (D → D) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_106 (A B C : Prop) : (A → B → C → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_107 (A B C : Prop) : (A → B → B → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_108 (A B C : Prop) : (A → B → C → (C → C) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_109 (A B : Prop) : (A → B → B → (B → B) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_110 (A B C D : Prop) : (A → B → C → (D → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_111 (A B C : Prop) : (A → B → C → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_112 (A B C : Prop) : (A → B → B → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_113 (A B C : Prop) : (A → B → C → (C → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_114 (A B : Prop) : (A → B → B → (B → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_115 (A B C : Prop) : (A → B → C → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_116 (A B : Prop) : (A → B → B → (A → A) → A) := by
  run_tac tactic_name
theorem propfmls_5_28_117 (A B C D : Prop) : (A → B → C → (C → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_28_118 (A B C : Prop) : (A → B → A → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_119 (A B C : Prop) : (A → A → B → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_120 (A B C : Prop) : (A → B → B → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_121 (A B : Prop) : (A → A → A → (A → B) → B) := by
  run_tac tactic_name
theorem propfmls_5_28_122 (A B C D : Prop) : (A → B → C → (B → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_28_123 (A B C : Prop) : (A → A → B → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_124 (A B C : Prop) : (A → B → A → (B → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_28_125 (A B C D : Prop) : (A → B → C → (A → D) → D) := by
  run_tac tactic_name
theorem propfmls_5_28_126 (A B C : Prop) : (A → B → B → (A → C) → C) := by
  run_tac tactic_name
theorem propfmls_5_29_1 (A B C D E : Prop) : ((((A → B) → C) → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_29_2 (A B C D : Prop) : ((((A → B) → C) → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_3 (A B C D : Prop) : ((((A → B) → C) → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_4 (A B C D : Prop) : ((((A → B) → A) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_5 (A B C D : Prop) : ((((A → A) → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_6 (A B C D : Prop) : ((((A → B) → C) → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_7 (A B C : Prop) : ((((A → A) → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_8 (A B C : Prop) : ((((A → B) → C) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_9 (A B C : Prop) : ((((A → B) → A) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_10 (A B C D : Prop) : ((((A → B) → C) → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_11 (A B C : Prop) : ((((A → B) → C) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_12 (A B C : Prop) : ((((A → A) → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_13 (A B C : Prop) : ((((A → B) → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_14 (A B C D : Prop) : ((((A → B) → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_15 (A B C : Prop) : ((((A → B) → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_16 (A B C : Prop) : ((((A → B) → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_17 (A B C : Prop) : ((((A → A) → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_18 (A B C D : Prop) : ((((A → B) → C) → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_19 (A B C : Prop) : ((((A → B) → A) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_20 (A B C : Prop) : ((((A → B) → C) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_21 (A B C : Prop) : ((((A → A) → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_22 (A B C : Prop) : ((((A → B) → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_23 (A B : Prop) : ((((A → A) → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_24 (A B : Prop) : ((((A → B) → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_25 (A B C : Prop) : ((((A → B) → C) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_26 (A B : Prop) : ((((A → B) → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_27 (A B : Prop) : ((((A → A) → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_28 (A B C D : Prop) : ((((A → B) → C) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_29 (A B C : Prop) : ((((A → B) → C) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_30 (A B C : Prop) : ((((A → B) → A) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_31 (A B C : Prop) : ((((A → A) → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_32 (A B C : Prop) : ((((A → B) → C) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_33 (A B : Prop) : ((((A → A) → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_34 (A B : Prop) : ((((A → B) → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_35 (A B C : Prop) : ((((A → B) → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_36 (A B : Prop) : ((((A → B) → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_37 (A B : Prop) : ((((A → A) → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_38 (A B C D : Prop) : ((((A → B) → C) → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_29_39 (A B C : Prop) : ((((A → B) → C) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_40 (A B C : Prop) : ((((A → B) → A) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_41 (A B C : Prop) : ((((A → A) → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_42 (A B C : Prop) : ((((A → B) → C) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_43 (A B : Prop) : ((((A → A) → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_44 (A B : Prop) : ((((A → B) → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_45 (A B C : Prop) : ((((A → B) → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_46 (A B : Prop) : ((((A → B) → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_47 (A B : Prop) : ((((A → A) → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_48 (A B C : Prop) : ((((A → B) → C) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_29_49 (A B : Prop) : ((((A → B) → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_50 (A B : Prop) : ((((A → A) → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_51 (A B : Prop) : ((((A → B) → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_29_52 (A : Prop) : ((((A → A) → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_29_53 (A B C D : Prop) : ((((A → B) → C) → D) → C → D) := by
  run_tac tactic_name
theorem propfmls_5_29_54 (A B C : Prop) : ((((A → B) → C) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_29_55 (A B C : Prop) : ((((A → B) → A) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_29_56 (A B C : Prop) : ((((A → A) → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_29_57 (A B C : Prop) : ((((A → B) → C) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_29_58 (A B : Prop) : ((((A → A) → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_29_59 (A B : Prop) : ((((A → B) → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_29_60 (A B C : Prop) : ((((A → B) → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_29_61 (A B : Prop) : ((((A → B) → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_29_62 (A B : Prop) : ((((A → A) → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_29_63 (A B C : Prop) : ((((A → B) → B) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_29_64 (A B : Prop) : ((((A → B) → B) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_30_1 (A B C D E : Prop) : (((A → B → C) → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_30_2 (A B C D : Prop) : (((A → B → C) → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_3 (A B C D : Prop) : (((A → B → C) → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_4 (A B C D : Prop) : (((A → B → A) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_5 (A B C D : Prop) : (((A → A → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_6 (A B C D : Prop) : (((A → B → C) → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_7 (A B C : Prop) : (((A → A → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_8 (A B C : Prop) : (((A → B → C) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_9 (A B C : Prop) : (((A → B → A) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_10 (A B C D : Prop) : (((A → B → C) → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_11 (A B C : Prop) : (((A → B → C) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_12 (A B C : Prop) : (((A → A → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_13 (A B C : Prop) : (((A → B → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_14 (A B C D : Prop) : (((A → B → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_15 (A B C : Prop) : (((A → B → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_16 (A B C : Prop) : (((A → B → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_17 (A B C : Prop) : (((A → A → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_18 (A B C D : Prop) : (((A → B → C) → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_19 (A B C : Prop) : (((A → B → A) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_20 (A B C : Prop) : (((A → B → C) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_21 (A B C : Prop) : (((A → A → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_22 (A B C : Prop) : (((A → B → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_23 (A B : Prop) : (((A → A → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_24 (A B : Prop) : (((A → B → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_25 (A B C : Prop) : (((A → B → C) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_26 (A B : Prop) : (((A → B → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_27 (A B : Prop) : (((A → A → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_28 (A B C D : Prop) : (((A → B → C) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_29 (A B C : Prop) : (((A → B → C) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_30 (A B C : Prop) : (((A → B → A) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_31 (A B C : Prop) : (((A → A → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_32 (A B C : Prop) : (((A → B → C) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_33 (A B : Prop) : (((A → A → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_34 (A B : Prop) : (((A → B → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_35 (A B C : Prop) : (((A → B → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_36 (A B : Prop) : (((A → B → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_37 (A B : Prop) : (((A → A → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_38 (A B C D : Prop) : (((A → B → C) → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_30_39 (A B C : Prop) : (((A → B → C) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_40 (A B C : Prop) : (((A → B → A) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_41 (A B C : Prop) : (((A → A → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_42 (A B C : Prop) : (((A → B → C) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_43 (A B : Prop) : (((A → A → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_44 (A B : Prop) : (((A → B → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_45 (A B C : Prop) : (((A → B → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_46 (A B : Prop) : (((A → B → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_47 (A B : Prop) : (((A → A → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_48 (A B C : Prop) : (((A → B → C) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_30_49 (A B : Prop) : (((A → B → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_50 (A B : Prop) : (((A → A → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_51 (A B : Prop) : (((A → B → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_30_52 (A : Prop) : (((A → A → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_30_53 (A B C D : Prop) : (((A → B → C) → D) → C → D) := by
  run_tac tactic_name
theorem propfmls_5_30_54 (A B C : Prop) : (((A → B → C) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_30_55 (A B C : Prop) : (((A → B → A) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_30_56 (A B C : Prop) : (((A → A → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_30_57 (A B C : Prop) : (((A → B → C) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_30_58 (A B : Prop) : (((A → A → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_30_59 (A B : Prop) : (((A → B → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_30_60 (A B C : Prop) : (((A → B → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_30_61 (A B : Prop) : (((A → B → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_30_62 (A B : Prop) : (((A → A → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_30_63 (A B C D : Prop) : (((A → B → B) → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_30_64 (A B C : Prop) : (((A → B → B) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_30_65 (A B C : Prop) : (((A → B → B) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_30_66 (A B C : Prop) : (((A → A → A) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_30_67 (A B C : Prop) : (((A → B → B) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_30_68 (A B : Prop) : (((A → A → A) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_30_69 (A B : Prop) : (((A → B → B) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_30_70 (A B C D : Prop) : (((A → B → A) → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_30_71 (A B C : Prop) : (((A → B → A) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_30_72 (A B C : Prop) : (((A → B → A) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_30_73 (A B C : Prop) : (((A → B → A) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_30_74 (A B : Prop) : (((A → B → A) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_31_1 (A B C D E : Prop) : ((A → (B → C) → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_31_2 (A B C D : Prop) : ((A → (B → C) → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_3 (A B C D : Prop) : ((A → (B → C) → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_4 (A B C D : Prop) : ((A → (B → A) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_5 (A B C D : Prop) : ((A → (A → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_6 (A B C D : Prop) : ((A → (B → C) → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_7 (A B C : Prop) : ((A → (A → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_8 (A B C : Prop) : ((A → (B → C) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_9 (A B C : Prop) : ((A → (B → A) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_10 (A B C D : Prop) : ((A → (B → C) → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_11 (A B C : Prop) : ((A → (B → C) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_12 (A B C : Prop) : ((A → (A → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_13 (A B C : Prop) : ((A → (B → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_14 (A B C D : Prop) : ((A → (B → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_15 (A B C : Prop) : ((A → (B → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_16 (A B C : Prop) : ((A → (B → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_17 (A B C : Prop) : ((A → (A → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_18 (A B C D : Prop) : ((A → (B → C) → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_19 (A B C : Prop) : ((A → (B → A) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_20 (A B C : Prop) : ((A → (B → C) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_21 (A B C : Prop) : ((A → (A → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_22 (A B C : Prop) : ((A → (B → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_23 (A B : Prop) : ((A → (A → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_24 (A B : Prop) : ((A → (B → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_25 (A B C : Prop) : ((A → (B → C) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_26 (A B : Prop) : ((A → (B → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_27 (A B : Prop) : ((A → (A → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_28 (A B C D : Prop) : ((A → (B → C) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_29 (A B C : Prop) : ((A → (B → C) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_30 (A B C : Prop) : ((A → (B → A) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_31 (A B C : Prop) : ((A → (A → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_32 (A B C : Prop) : ((A → (B → C) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_33 (A B : Prop) : ((A → (A → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_34 (A B : Prop) : ((A → (B → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_35 (A B C : Prop) : ((A → (B → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_36 (A B : Prop) : ((A → (B → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_37 (A B : Prop) : ((A → (A → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_38 (A B C D : Prop) : ((A → (B → C) → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_31_39 (A B C : Prop) : ((A → (B → C) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_40 (A B C : Prop) : ((A → (B → A) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_41 (A B C : Prop) : ((A → (A → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_42 (A B C : Prop) : ((A → (B → C) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_43 (A B : Prop) : ((A → (A → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_44 (A B : Prop) : ((A → (B → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_45 (A B C : Prop) : ((A → (B → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_46 (A B : Prop) : ((A → (B → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_47 (A B : Prop) : ((A → (A → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_48 (A B C : Prop) : ((A → (B → C) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_31_49 (A B : Prop) : ((A → (B → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_50 (A B : Prop) : ((A → (A → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_51 (A B : Prop) : ((A → (B → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_31_52 (A : Prop) : ((A → (A → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_31_53 (A B C : Prop) : ((A → (B → A) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_31_54 (A B : Prop) : ((A → (B → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_31_55 (A B : Prop) : ((A → (A → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_31_56 (A B C : Prop) : ((A → (B → B) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_31_57 (A B : Prop) : ((A → (B → B) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_32_1 (A B C D E : Prop) : (A → ((B → C) → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_32_2 (A B C D : Prop) : (A → ((B → C) → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_3 (A B C D : Prop) : (A → ((B → C) → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_4 (A B C D : Prop) : (A → ((B → A) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_5 (A B C D : Prop) : (A → ((A → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_6 (A B C D : Prop) : (A → ((B → C) → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_7 (A B C : Prop) : (A → ((A → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_8 (A B C : Prop) : (A → ((B → C) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_9 (A B C : Prop) : (A → ((B → A) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_10 (A B C D : Prop) : (A → ((B → C) → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_11 (A B C : Prop) : (A → ((B → C) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_12 (A B C : Prop) : (A → ((A → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_13 (A B C : Prop) : (A → ((B → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_14 (A B C D : Prop) : (A → ((B → B) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_15 (A B C : Prop) : (A → ((B → B) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_16 (A B C : Prop) : (A → ((B → B) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_17 (A B C : Prop) : (A → ((A → A) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_18 (A B C D : Prop) : (A → ((B → C) → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_19 (A B C : Prop) : (A → ((B → A) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_20 (A B C : Prop) : (A → ((B → C) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_21 (A B C : Prop) : (A → ((A → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_22 (A B C : Prop) : (A → ((B → B) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_23 (A B : Prop) : (A → ((A → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_24 (A B : Prop) : (A → ((B → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_25 (A B C : Prop) : (A → ((B → C) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_26 (A B : Prop) : (A → ((B → A) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_27 (A B : Prop) : (A → ((A → B) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_28 (A B C D : Prop) : (A → ((B → C) → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_29 (A B C : Prop) : (A → ((B → C) → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_30 (A B C : Prop) : (A → ((B → A) → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_31 (A B C : Prop) : (A → ((A → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_32 (A B C : Prop) : (A → ((B → C) → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_33 (A B : Prop) : (A → ((A → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_34 (A B : Prop) : (A → ((B → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_35 (A B C : Prop) : (A → ((B → B) → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_36 (A B : Prop) : (A → ((B → B) → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_37 (A B : Prop) : (A → ((A → A) → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_38 (A B C D : Prop) : (A → ((B → C) → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_32_39 (A B C : Prop) : (A → ((B → C) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_40 (A B C : Prop) : (A → ((B → A) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_41 (A B C : Prop) : (A → ((A → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_42 (A B C : Prop) : (A → ((B → C) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_43 (A B : Prop) : (A → ((A → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_44 (A B : Prop) : (A → ((B → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_45 (A B C : Prop) : (A → ((B → B) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_46 (A B : Prop) : (A → ((B → B) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_47 (A B : Prop) : (A → ((A → A) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_48 (A B C : Prop) : (A → ((B → C) → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_32_49 (A B : Prop) : (A → ((B → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_50 (A B : Prop) : (A → ((A → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_51 (A B : Prop) : (A → ((B → B) → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_32_52 (A : Prop) : (A → ((A → A) → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_32_53 (A B C D E : Prop) : (A → ((B → C) → D) → E → A) := by
  run_tac tactic_name
theorem propfmls_5_32_54 (A B C D : Prop) : (A → ((A → B) → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_55 (A B C D : Prop) : (A → ((B → C) → D) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_56 (A B C D : Prop) : (A → ((B → C) → B) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_57 (A B C D : Prop) : (A → ((B → B) → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_58 (A B C D : Prop) : (A → ((B → A) → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_59 (A B C : Prop) : (A → ((A → A) → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_60 (A B C : Prop) : (A → ((B → A) → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_61 (A B C : Prop) : (A → ((B → A) → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_62 (A B C D : Prop) : (A → ((B → C) → D) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_63 (A B C : Prop) : (A → ((A → B) → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_64 (A B C : Prop) : (A → ((B → B) → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_65 (A B C : Prop) : (A → ((B → C) → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_66 (A B C D : Prop) : (A → ((B → C) → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_67 (A B C : Prop) : (A → ((A → B) → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_68 (A B C : Prop) : (A → ((B → C) → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_69 (A B C : Prop) : (A → ((B → B) → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_70 (A B C D : Prop) : (A → ((B → C) → A) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_71 (A B C : Prop) : (A → ((A → B) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_72 (A B C : Prop) : (A → ((B → C) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_73 (A B C : Prop) : (A → ((B → B) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_74 (A B C : Prop) : (A → ((B → A) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_75 (A B : Prop) : (A → ((A → A) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_76 (A B : Prop) : (A → ((B → A) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_77 (A B C : Prop) : (A → ((B → C) → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_78 (A B : Prop) : (A → ((A → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_79 (A B : Prop) : (A → ((B → B) → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_80 (A B C D : Prop) : (A → ((B → C) → D) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_32_81 (A B C : Prop) : (A → ((A → B) → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_82 (A B C : Prop) : (A → ((B → C) → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_83 (A B C : Prop) : (A → ((B → B) → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_84 (A B C : Prop) : (A → ((B → A) → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_85 (A B : Prop) : (A → ((A → A) → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_86 (A B : Prop) : (A → ((B → A) → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_87 (A B C : Prop) : (A → ((B → C) → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_32_88 (A B : Prop) : (A → ((A → B) → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_89 (A B : Prop) : (A → ((B → B) → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_32_90 (A B C D : Prop) : (A → ((B → C) → D) → C → D) := by
  run_tac tactic_name
theorem propfmls_5_32_91 (A B C : Prop) : (A → ((B → A) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_32_92 (A B C : Prop) : (A → ((A → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_32_93 (A B C : Prop) : (A → ((B → C) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_32_94 (A B : Prop) : (A → ((B → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_32_95 (A B C : Prop) : (A → ((B → B) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_32_96 (A B : Prop) : (A → ((A → A) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_32_97 (A B C D : Prop) : (A → ((B → A) → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_32_98 (A B C : Prop) : (A → ((B → A) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_32_99 (A B C : Prop) : (A → ((B → A) → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_32_100 (A B C : Prop) : (A → ((A → A) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_32_101 (A B C D : Prop) : (A → ((B → B) → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_32_102 (A B C : Prop) : (A → ((B → B) → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_32_103 (A B C : Prop) : (A → ((B → B) → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_32_104 (A B : Prop) : (A → ((B → B) → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_33_1 (A B C D E : Prop) : (((A → B) → C → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_33_2 (A B C D : Prop) : (((A → B) → C → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_3 (A B C D : Prop) : (((A → B) → C → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_4 (A B C D : Prop) : (((A → B) → A → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_5 (A B C D : Prop) : (((A → A) → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_6 (A B C D : Prop) : (((A → B) → C → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_7 (A B C : Prop) : (((A → A) → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_8 (A B C : Prop) : (((A → B) → C → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_9 (A B C : Prop) : (((A → B) → A → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_10 (A B C D : Prop) : (((A → B) → C → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_11 (A B C : Prop) : (((A → B) → C → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_12 (A B C : Prop) : (((A → A) → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_13 (A B C : Prop) : (((A → B) → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_14 (A B C D : Prop) : (((A → B) → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_15 (A B C : Prop) : (((A → B) → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_16 (A B C : Prop) : (((A → B) → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_17 (A B C : Prop) : (((A → A) → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_18 (A B C D : Prop) : (((A → B) → C → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_19 (A B C : Prop) : (((A → B) → A → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_20 (A B C : Prop) : (((A → B) → C → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_21 (A B C : Prop) : (((A → A) → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_22 (A B C : Prop) : (((A → B) → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_23 (A B : Prop) : (((A → A) → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_24 (A B : Prop) : (((A → B) → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_25 (A B C : Prop) : (((A → B) → C → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_26 (A B : Prop) : (((A → B) → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_27 (A B : Prop) : (((A → A) → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_28 (A B C D : Prop) : (((A → B) → C → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_29 (A B C : Prop) : (((A → B) → C → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_30 (A B C : Prop) : (((A → B) → A → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_31 (A B C : Prop) : (((A → A) → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_32 (A B C : Prop) : (((A → B) → C → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_33 (A B : Prop) : (((A → A) → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_34 (A B : Prop) : (((A → B) → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_35 (A B C : Prop) : (((A → B) → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_36 (A B : Prop) : (((A → B) → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_37 (A B : Prop) : (((A → A) → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_38 (A B C D : Prop) : (((A → B) → C → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_33_39 (A B C : Prop) : (((A → B) → C → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_40 (A B C : Prop) : (((A → B) → A → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_41 (A B C : Prop) : (((A → A) → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_42 (A B C : Prop) : (((A → B) → C → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_43 (A B : Prop) : (((A → A) → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_44 (A B : Prop) : (((A → B) → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_45 (A B C : Prop) : (((A → B) → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_46 (A B : Prop) : (((A → B) → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_47 (A B : Prop) : (((A → A) → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_48 (A B C : Prop) : (((A → B) → C → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_33_49 (A B : Prop) : (((A → B) → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_50 (A B : Prop) : (((A → A) → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_51 (A B : Prop) : (((A → B) → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_33_52 (A : Prop) : (((A → A) → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_33_53 (A B C : Prop) : (((A → B) → B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_33_54 (A B : Prop) : (((A → B) → B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_33_55 (A B : Prop) : (((A → A) → A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_33_56 (A B C : Prop) : (((A → A) → B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_33_57 (A B : Prop) : (((A → A) → B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_34_1 (A B C D E : Prop) : ((A → B → C → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_34_2 (A B C D : Prop) : ((A → B → C → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_3 (A B C D : Prop) : ((A → B → C → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_4 (A B C D : Prop) : ((A → B → A → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_5 (A B C D : Prop) : ((A → A → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_6 (A B C D : Prop) : ((A → B → C → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_7 (A B C : Prop) : ((A → A → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_8 (A B C : Prop) : ((A → B → C → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_9 (A B C : Prop) : ((A → B → A → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_10 (A B C D : Prop) : ((A → B → C → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_11 (A B C : Prop) : ((A → B → C → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_12 (A B C : Prop) : ((A → A → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_13 (A B C : Prop) : ((A → B → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_14 (A B C D : Prop) : ((A → B → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_15 (A B C : Prop) : ((A → B → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_16 (A B C : Prop) : ((A → B → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_17 (A B C : Prop) : ((A → A → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_18 (A B C D : Prop) : ((A → B → C → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_19 (A B C : Prop) : ((A → B → A → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_20 (A B C : Prop) : ((A → B → C → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_21 (A B C : Prop) : ((A → A → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_22 (A B C : Prop) : ((A → B → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_23 (A B : Prop) : ((A → A → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_24 (A B : Prop) : ((A → B → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_25 (A B C : Prop) : ((A → B → C → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_26 (A B : Prop) : ((A → B → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_27 (A B : Prop) : ((A → A → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_28 (A B C D : Prop) : ((A → B → C → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_29 (A B C : Prop) : ((A → B → C → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_30 (A B C : Prop) : ((A → B → A → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_31 (A B C : Prop) : ((A → A → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_32 (A B C : Prop) : ((A → B → C → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_33 (A B : Prop) : ((A → A → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_34 (A B : Prop) : ((A → B → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_35 (A B C : Prop) : ((A → B → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_36 (A B : Prop) : ((A → B → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_37 (A B : Prop) : ((A → A → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_38 (A B C D : Prop) : ((A → B → C → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_34_39 (A B C : Prop) : ((A → B → C → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_40 (A B C : Prop) : ((A → B → A → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_41 (A B C : Prop) : ((A → A → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_42 (A B C : Prop) : ((A → B → C → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_43 (A B : Prop) : ((A → A → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_44 (A B : Prop) : ((A → B → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_45 (A B C : Prop) : ((A → B → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_46 (A B : Prop) : ((A → B → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_47 (A B : Prop) : ((A → A → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_48 (A B C : Prop) : ((A → B → C → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_34_49 (A B : Prop) : ((A → B → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_50 (A B : Prop) : ((A → A → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_51 (A B : Prop) : ((A → B → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_34_52 (A : Prop) : ((A → A → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_34_53 (A B : Prop) : ((A → A → A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_35_1 (A B C D E : Prop) : (A → (B → C → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_35_2 (A B C D : Prop) : (A → (B → C → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_3 (A B C D : Prop) : (A → (B → C → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_4 (A B C D : Prop) : (A → (B → A → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_5 (A B C D : Prop) : (A → (A → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_6 (A B C D : Prop) : (A → (B → C → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_7 (A B C : Prop) : (A → (A → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_8 (A B C : Prop) : (A → (B → C → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_9 (A B C : Prop) : (A → (B → A → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_10 (A B C D : Prop) : (A → (B → C → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_11 (A B C : Prop) : (A → (B → C → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_12 (A B C : Prop) : (A → (A → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_13 (A B C : Prop) : (A → (B → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_14 (A B C D : Prop) : (A → (B → B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_15 (A B C : Prop) : (A → (B → B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_16 (A B C : Prop) : (A → (B → B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_17 (A B C : Prop) : (A → (A → A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_18 (A B C D : Prop) : (A → (B → C → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_19 (A B C : Prop) : (A → (B → A → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_20 (A B C : Prop) : (A → (B → C → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_21 (A B C : Prop) : (A → (A → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_22 (A B C : Prop) : (A → (B → B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_23 (A B : Prop) : (A → (A → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_24 (A B : Prop) : (A → (B → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_25 (A B C : Prop) : (A → (B → C → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_26 (A B : Prop) : (A → (B → A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_27 (A B : Prop) : (A → (A → B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_28 (A B C D : Prop) : (A → (B → C → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_29 (A B C : Prop) : (A → (B → C → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_30 (A B C : Prop) : (A → (B → A → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_31 (A B C : Prop) : (A → (A → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_32 (A B C : Prop) : (A → (B → C → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_33 (A B : Prop) : (A → (A → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_34 (A B : Prop) : (A → (B → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_35 (A B C : Prop) : (A → (B → B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_36 (A B : Prop) : (A → (B → B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_37 (A B : Prop) : (A → (A → A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_38 (A B C D : Prop) : (A → (B → C → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_35_39 (A B C : Prop) : (A → (B → C → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_40 (A B C : Prop) : (A → (B → A → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_41 (A B C : Prop) : (A → (A → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_42 (A B C : Prop) : (A → (B → C → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_43 (A B : Prop) : (A → (A → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_44 (A B : Prop) : (A → (B → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_45 (A B C : Prop) : (A → (B → B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_46 (A B : Prop) : (A → (B → B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_47 (A B : Prop) : (A → (A → A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_48 (A B C : Prop) : (A → (B → C → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_35_49 (A B : Prop) : (A → (B → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_50 (A B : Prop) : (A → (A → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_51 (A B : Prop) : (A → (B → B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_35_52 (A : Prop) : (A → (A → A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_35_53 (A B C D E : Prop) : (A → (B → C → D) → E → A) := by
  run_tac tactic_name
theorem propfmls_5_35_54 (A B C D : Prop) : (A → (A → B → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_55 (A B C D : Prop) : (A → (B → C → D) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_56 (A B C D : Prop) : (A → (B → C → B) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_57 (A B C D : Prop) : (A → (B → B → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_58 (A B C D : Prop) : (A → (B → A → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_59 (A B C : Prop) : (A → (A → A → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_60 (A B C : Prop) : (A → (B → A → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_61 (A B C : Prop) : (A → (B → A → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_62 (A B C D : Prop) : (A → (B → C → D) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_63 (A B C : Prop) : (A → (A → B → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_64 (A B C : Prop) : (A → (B → B → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_65 (A B C : Prop) : (A → (B → C → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_66 (A B C D : Prop) : (A → (B → C → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_67 (A B C : Prop) : (A → (A → B → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_68 (A B C : Prop) : (A → (B → C → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_69 (A B C : Prop) : (A → (B → B → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_70 (A B C D : Prop) : (A → (B → C → A) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_71 (A B C : Prop) : (A → (A → B → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_72 (A B C : Prop) : (A → (B → C → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_73 (A B C : Prop) : (A → (B → B → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_74 (A B C : Prop) : (A → (B → A → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_75 (A B : Prop) : (A → (A → A → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_76 (A B : Prop) : (A → (B → A → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_77 (A B C : Prop) : (A → (B → C → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_78 (A B : Prop) : (A → (A → B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_79 (A B : Prop) : (A → (B → B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_80 (A B C D : Prop) : (A → (B → C → D) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_35_81 (A B C : Prop) : (A → (A → B → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_82 (A B C : Prop) : (A → (B → C → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_83 (A B C : Prop) : (A → (B → B → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_84 (A B C : Prop) : (A → (B → A → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_85 (A B : Prop) : (A → (A → A → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_86 (A B : Prop) : (A → (B → A → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_87 (A B C : Prop) : (A → (B → C → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_35_88 (A B : Prop) : (A → (A → B → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_89 (A B : Prop) : (A → (B → B → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_35_90 (A B C : Prop) : (A → (B → B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_35_91 (A B : Prop) : (A → (A → A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_35_92 (A B C : Prop) : (A → (A → B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_35_93 (A B C : Prop) : (A → (B → A → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_35_94 (A B C : Prop) : (A → (A → A → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_36_1 (A B C D E : Prop) : ((A → B) → (C → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_36_2 (A B C D : Prop) : ((A → B) → (C → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_3 (A B C D : Prop) : ((A → B) → (C → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_4 (A B C D : Prop) : ((A → B) → (A → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_5 (A B C D : Prop) : ((A → A) → (B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_6 (A B C D : Prop) : ((A → B) → (C → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_7 (A B C : Prop) : ((A → A) → (B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_8 (A B C : Prop) : ((A → B) → (C → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_9 (A B C : Prop) : ((A → B) → (A → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_10 (A B C D : Prop) : ((A → B) → (C → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_11 (A B C : Prop) : ((A → B) → (C → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_12 (A B C : Prop) : ((A → A) → (B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_13 (A B C : Prop) : ((A → B) → (A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_14 (A B C D : Prop) : ((A → B) → (B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_15 (A B C : Prop) : ((A → B) → (B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_16 (A B C : Prop) : ((A → B) → (B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_17 (A B C : Prop) : ((A → A) → (A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_18 (A B C D : Prop) : ((A → B) → (C → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_19 (A B C : Prop) : ((A → B) → (A → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_20 (A B C : Prop) : ((A → B) → (C → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_21 (A B C : Prop) : ((A → A) → (B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_22 (A B C : Prop) : ((A → B) → (B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_23 (A B : Prop) : ((A → A) → (A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_24 (A B : Prop) : ((A → B) → (B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_25 (A B C : Prop) : ((A → B) → (C → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_26 (A B : Prop) : ((A → B) → (A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_27 (A B : Prop) : ((A → A) → (B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_28 (A B C D : Prop) : ((A → B) → (C → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_29 (A B C : Prop) : ((A → B) → (C → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_30 (A B C : Prop) : ((A → B) → (A → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_31 (A B C : Prop) : ((A → A) → (B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_32 (A B C : Prop) : ((A → B) → (C → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_33 (A B : Prop) : ((A → A) → (B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_34 (A B : Prop) : ((A → B) → (A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_35 (A B C : Prop) : ((A → B) → (B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_36 (A B : Prop) : ((A → B) → (B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_37 (A B : Prop) : ((A → A) → (A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_38 (A B C D : Prop) : ((A → B) → (C → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_36_39 (A B C : Prop) : ((A → B) → (C → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_40 (A B C : Prop) : ((A → B) → (A → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_41 (A B C : Prop) : ((A → A) → (B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_42 (A B C : Prop) : ((A → B) → (C → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_43 (A B : Prop) : ((A → A) → (B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_44 (A B : Prop) : ((A → B) → (A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_45 (A B C : Prop) : ((A → B) → (B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_46 (A B : Prop) : ((A → B) → (B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_47 (A B : Prop) : ((A → A) → (A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_48 (A B C : Prop) : ((A → B) → (C → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_36_49 (A B : Prop) : ((A → B) → (A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_50 (A B : Prop) : ((A → A) → (B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_51 (A B : Prop) : ((A → B) → (B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_36_52 (A : Prop) : ((A → A) → (A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_36_53 (A B C D : Prop) : ((A → B) → (C → D) → C → D) := by
  run_tac tactic_name
theorem propfmls_5_36_54 (A B C : Prop) : ((A → B) → (C → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_36_55 (A B C : Prop) : ((A → B) → (A → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_36_56 (A B C : Prop) : ((A → A) → (B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_36_57 (A B C : Prop) : ((A → B) → (C → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_36_58 (A B : Prop) : ((A → A) → (B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_36_59 (A B : Prop) : ((A → B) → (A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_60 (A B C : Prop) : ((A → B) → (B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_36_61 (A B : Prop) : ((A → B) → (B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_36_62 (A B : Prop) : ((A → A) → (A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_63 (A B C D : Prop) : ((A → B) → (C → D) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_64 (A B C : Prop) : ((A → B) → (B → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_65 (A B C : Prop) : ((A → B) → (A → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_66 (A B C : Prop) : ((A → B) → (C → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_67 (A B C : Prop) : ((A → B) → (C → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_68 (A B : Prop) : ((A → B) → (B → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_69 (A B C : Prop) : ((A → B) → (C → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_70 (A B : Prop) : ((A → B) → (B → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_71 (A B : Prop) : ((A → B) → (A → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_36_72 (A B C : Prop) : ((A → B) → (B → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_36_73 (A B C : Prop) : ((A → B) → (C → A) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_1 (A B C D E : Prop) : (A → B → (C → D) → E → E) := by
  run_tac tactic_name
theorem propfmls_5_37_2 (A B C D : Prop) : (A → B → (C → D) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_3 (A B C D : Prop) : (A → B → (C → A) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_4 (A B C D : Prop) : (A → B → (A → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_5 (A B C D : Prop) : (A → A → (B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_6 (A B C D : Prop) : (A → B → (C → D) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_7 (A B C : Prop) : (A → A → (B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_8 (A B C : Prop) : (A → B → (C → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_9 (A B C : Prop) : (A → B → (A → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_10 (A B C D : Prop) : (A → B → (C → B) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_11 (A B C : Prop) : (A → B → (C → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_12 (A B C : Prop) : (A → A → (B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_13 (A B C : Prop) : (A → B → (A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_14 (A B C D : Prop) : (A → B → (B → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_15 (A B C : Prop) : (A → B → (B → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_16 (A B C : Prop) : (A → B → (B → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_17 (A B C : Prop) : (A → A → (A → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_18 (A B C D : Prop) : (A → B → (C → D) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_19 (A B C : Prop) : (A → B → (A → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_20 (A B C : Prop) : (A → B → (C → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_21 (A B C : Prop) : (A → A → (B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_22 (A B C : Prop) : (A → B → (B → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_23 (A B : Prop) : (A → A → (A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_24 (A B : Prop) : (A → B → (B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_25 (A B C : Prop) : (A → B → (C → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_26 (A B : Prop) : (A → B → (A → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_27 (A B : Prop) : (A → A → (B → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_28 (A B C D : Prop) : (A → B → (C → C) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_29 (A B C : Prop) : (A → B → (C → C) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_30 (A B C : Prop) : (A → B → (A → A) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_31 (A B C : Prop) : (A → A → (B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_32 (A B C : Prop) : (A → B → (C → C) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_33 (A B : Prop) : (A → A → (B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_34 (A B : Prop) : (A → B → (A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_35 (A B C : Prop) : (A → B → (B → B) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_36 (A B : Prop) : (A → B → (B → B) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_37 (A B : Prop) : (A → A → (A → A) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_38 (A B C D : Prop) : (A → B → (C → D) → D → D) := by
  run_tac tactic_name
theorem propfmls_5_37_39 (A B C : Prop) : (A → B → (C → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_40 (A B C : Prop) : (A → B → (A → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_41 (A B C : Prop) : (A → A → (B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_42 (A B C : Prop) : (A → B → (C → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_43 (A B : Prop) : (A → A → (B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_44 (A B : Prop) : (A → B → (A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_45 (A B C : Prop) : (A → B → (B → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_46 (A B : Prop) : (A → B → (B → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_47 (A B : Prop) : (A → A → (A → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_48 (A B C : Prop) : (A → B → (C → C) → C → C) := by
  run_tac tactic_name
theorem propfmls_5_37_49 (A B : Prop) : (A → B → (A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_50 (A B : Prop) : (A → A → (B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_51 (A B : Prop) : (A → B → (B → B) → B → B) := by
  run_tac tactic_name
theorem propfmls_5_37_52 (A : Prop) : (A → A → (A → A) → A → A) := by
  run_tac tactic_name
theorem propfmls_5_37_53 (A B C D E : Prop) : (A → B → (C → D) → E → B) := by
  run_tac tactic_name
theorem propfmls_5_37_54 (A B C D : Prop) : (A → A → (B → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_55 (A B C D : Prop) : (A → B → (C → D) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_56 (A B C D : Prop) : (A → B → (C → A) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_57 (A B C D : Prop) : (A → B → (A → C) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_58 (A B C D : Prop) : (A → B → (B → C) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_59 (A B C : Prop) : (A → A → (A → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_60 (A B C : Prop) : (A → B → (B → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_61 (A B C : Prop) : (A → B → (B → A) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_62 (A B C D : Prop) : (A → B → (C → D) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_63 (A B C : Prop) : (A → A → (B → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_64 (A B C : Prop) : (A → B → (A → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_65 (A B C : Prop) : (A → B → (C → A) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_66 (A B C D : Prop) : (A → B → (C → C) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_67 (A B C : Prop) : (A → A → (B → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_68 (A B C : Prop) : (A → B → (C → C) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_69 (A B C : Prop) : (A → B → (A → A) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_70 (A B C D : Prop) : (A → B → (C → B) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_71 (A B C : Prop) : (A → A → (B → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_72 (A B C : Prop) : (A → B → (C → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_73 (A B C : Prop) : (A → B → (A → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_74 (A B C : Prop) : (A → B → (B → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_75 (A B : Prop) : (A → A → (A → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_76 (A B : Prop) : (A → B → (B → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_77 (A B C : Prop) : (A → B → (C → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_78 (A B : Prop) : (A → A → (B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_79 (A B : Prop) : (A → B → (A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_80 (A B C D : Prop) : (A → B → (C → D) → D → B) := by
  run_tac tactic_name
theorem propfmls_5_37_81 (A B C : Prop) : (A → A → (B → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_82 (A B C : Prop) : (A → B → (C → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_83 (A B C : Prop) : (A → B → (A → C) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_84 (A B C : Prop) : (A → B → (B → C) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_85 (A B : Prop) : (A → A → (A → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_86 (A B : Prop) : (A → B → (B → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_87 (A B C : Prop) : (A → B → (C → C) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_88 (A B : Prop) : (A → A → (B → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_89 (A B : Prop) : (A → B → (A → A) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_90 (A B C D E : Prop) : (A → B → (C → D) → E → A) := by
  run_tac tactic_name
theorem propfmls_5_37_91 (A B C D : Prop) : (A → B → (C → D) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_92 (A B C D : Prop) : (A → B → (C → B) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_93 (A B C D : Prop) : (A → B → (B → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_94 (A B C D : Prop) : (A → B → (A → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_95 (A B C : Prop) : (A → B → (A → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_96 (A B C : Prop) : (A → B → (A → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_97 (A B C D : Prop) : (A → B → (C → D) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_98 (A B C : Prop) : (A → B → (B → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_99 (A B C : Prop) : (A → B → (C → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_100 (A B C D : Prop) : (A → B → (C → C) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_101 (A B C : Prop) : (A → B → (C → C) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_102 (A B C : Prop) : (A → B → (B → B) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_103 (A B C D : Prop) : (A → B → (C → A) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_104 (A B C : Prop) : (A → B → (C → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_105 (A B C : Prop) : (A → B → (B → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_106 (A B C : Prop) : (A → B → (A → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_107 (A B : Prop) : (A → B → (A → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_108 (A B C : Prop) : (A → B → (C → A) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_109 (A B : Prop) : (A → B → (B → A) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_110 (A B C D : Prop) : (A → B → (C → D) → D → A) := by
  run_tac tactic_name
theorem propfmls_5_37_111 (A B C : Prop) : (A → B → (C → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_112 (A B C : Prop) : (A → B → (B → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_113 (A B C : Prop) : (A → B → (A → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_114 (A B : Prop) : (A → B → (A → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_115 (A B C : Prop) : (A → B → (C → C) → C → A) := by
  run_tac tactic_name
theorem propfmls_5_37_116 (A B : Prop) : (A → B → (B → B) → B → A) := by
  run_tac tactic_name
theorem propfmls_5_37_117 (A B C D : Prop) : (A → B → (C → D) → C → D) := by
  run_tac tactic_name
theorem propfmls_5_37_118 (A B C : Prop) : (A → B → (A → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_37_119 (A B C : Prop) : (A → A → (B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_37_120 (A B C : Prop) : (A → B → (B → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_37_121 (A B : Prop) : (A → A → (A → B) → A → B) := by
  run_tac tactic_name
theorem propfmls_5_37_122 (A B C D : Prop) : (A → B → (B → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_37_123 (A B C : Prop) : (A → B → (B → C) → A → C) := by
  run_tac tactic_name
theorem propfmls_5_37_124 (A B C : Prop) : (A → A → (A → B) → C → B) := by
  run_tac tactic_name
theorem propfmls_5_37_125 (A B C D : Prop) : (A → B → (A → C) → D → C) := by
  run_tac tactic_name
theorem propfmls_5_37_126 (A B C : Prop) : (A → B → (A → C) → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_1 (A B C D E : Prop) : (((A → B) → C) → D → E → E) := by
  run_tac tactic_name
theorem propfmls_5_38_2 (A B C D : Prop) : (((A → B) → C) → D → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_3 (A B C D : Prop) : (((A → B) → C) → A → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_4 (A B C D : Prop) : (((A → B) → A) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_5 (A B C D : Prop) : (((A → A) → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_6 (A B C D : Prop) : (((A → B) → C) → D → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_7 (A B C : Prop) : (((A → A) → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_8 (A B C : Prop) : (((A → B) → C) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_9 (A B C : Prop) : (((A → B) → A) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_10 (A B C D : Prop) : (((A → B) → C) → B → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_11 (A B C : Prop) : (((A → B) → C) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_12 (A B C : Prop) : (((A → A) → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_13 (A B C : Prop) : (((A → B) → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_14 (A B C D : Prop) : (((A → B) → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_15 (A B C : Prop) : (((A → B) → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_16 (A B C : Prop) : (((A → B) → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_17 (A B C : Prop) : (((A → A) → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_18 (A B C D : Prop) : (((A → B) → C) → D → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_19 (A B C : Prop) : (((A → B) → A) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_20 (A B C : Prop) : (((A → B) → C) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_21 (A B C : Prop) : (((A → A) → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_22 (A B C : Prop) : (((A → B) → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_23 (A B : Prop) : (((A → A) → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_24 (A B : Prop) : (((A → B) → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_25 (A B C : Prop) : (((A → B) → C) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_26 (A B : Prop) : (((A → B) → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_27 (A B : Prop) : (((A → A) → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_28 (A B C D : Prop) : (((A → B) → C) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_29 (A B C : Prop) : (((A → B) → C) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_30 (A B C : Prop) : (((A → B) → A) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_31 (A B C : Prop) : (((A → A) → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_32 (A B C : Prop) : (((A → B) → C) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_33 (A B : Prop) : (((A → A) → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_34 (A B : Prop) : (((A → B) → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_35 (A B C : Prop) : (((A → B) → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_36 (A B : Prop) : (((A → B) → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_37 (A B : Prop) : (((A → A) → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_38 (A B C D : Prop) : (((A → B) → C) → D → D → D) := by
  run_tac tactic_name
theorem propfmls_5_38_39 (A B C : Prop) : (((A → B) → C) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_40 (A B C : Prop) : (((A → B) → A) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_41 (A B C : Prop) : (((A → A) → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_42 (A B C : Prop) : (((A → B) → C) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_43 (A B : Prop) : (((A → A) → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_44 (A B : Prop) : (((A → B) → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_45 (A B C : Prop) : (((A → B) → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_46 (A B : Prop) : (((A → B) → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_47 (A B : Prop) : (((A → A) → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_48 (A B C : Prop) : (((A → B) → C) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_38_49 (A B : Prop) : (((A → B) → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_50 (A B : Prop) : (((A → A) → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_51 (A B : Prop) : (((A → B) → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_38_52 (A : Prop) : (((A → A) → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_38_53 (A B C D E : Prop) : (((A → B) → C) → D → E → D) := by
  run_tac tactic_name
theorem propfmls_5_38_54 (A B C D : Prop) : (((A → B) → C) → A → D → A) := by
  run_tac tactic_name
theorem propfmls_5_38_55 (A B C D : Prop) : (((A → B) → C) → D → A → D) := by
  run_tac tactic_name
theorem propfmls_5_38_56 (A B C D : Prop) : (((A → B) → A) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_38_57 (A B C D : Prop) : (((A → A) → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_38_58 (A B C D : Prop) : (((A → B) → C) → B → D → B) := by
  run_tac tactic_name
theorem propfmls_5_38_59 (A B C : Prop) : (((A → A) → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_60 (A B C : Prop) : (((A → B) → C) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_61 (A B C : Prop) : (((A → B) → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_62 (A B C D : Prop) : (((A → B) → C) → D → B → D) := by
  run_tac tactic_name
theorem propfmls_5_38_63 (A B C : Prop) : (((A → B) → C) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_64 (A B C : Prop) : (((A → A) → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_38_65 (A B C : Prop) : (((A → B) → A) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_66 (A B C D : Prop) : (((A → B) → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_38_67 (A B C : Prop) : (((A → B) → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_68 (A B C : Prop) : (((A → B) → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_38_69 (A B C : Prop) : (((A → A) → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_70 (A B C D : Prop) : (((A → B) → C) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_38_71 (A B C : Prop) : (((A → B) → A) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_72 (A B C : Prop) : (((A → B) → C) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_38_73 (A B C : Prop) : (((A → A) → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_74 (A B C : Prop) : (((A → B) → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_75 (A B : Prop) : (((A → A) → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_76 (A B : Prop) : (((A → B) → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_77 (A B C : Prop) : (((A → B) → C) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_78 (A B : Prop) : (((A → B) → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_79 (A B : Prop) : (((A → A) → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_80 (A B C D : Prop) : (((A → B) → C) → D → C → D) := by
  run_tac tactic_name
theorem propfmls_5_38_81 (A B C : Prop) : (((A → B) → C) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_82 (A B C : Prop) : (((A → B) → A) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_38_83 (A B C : Prop) : (((A → A) → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_84 (A B C : Prop) : (((A → B) → C) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_85 (A B : Prop) : (((A → A) → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_86 (A B : Prop) : (((A → B) → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_87 (A B C : Prop) : (((A → B) → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_88 (A B : Prop) : (((A → B) → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_89 (A B : Prop) : (((A → A) → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_90 (A B C D : Prop) : (((A → B) → C) → D → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_91 (A B C : Prop) : (((A → B) → A) → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_92 (A B C : Prop) : (((A → A) → B) → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_93 (A B C : Prop) : (((A → B) → C) → A → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_94 (A B C : Prop) : (((A → B) → C) → B → B → C) := by
  run_tac tactic_name
theorem propfmls_5_38_95 (A B : Prop) : (((A → B) → A) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_38_96 (A B : Prop) : (((A → A) → B) → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_38_97 (A B C D : Prop) : (((A → B) → C) → B → D → C) := by
  run_tac tactic_name
theorem propfmls_5_38_98 (A B C : Prop) : (((A → B) → A) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_99 (A B C : Prop) : (((A → B) → C) → B → A → C) := by
  run_tac tactic_name
theorem propfmls_5_38_100 (A B C : Prop) : (((A → A) → B) → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_101 (A B C D : Prop) : (((A → A) → B) → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_38_102 (A B C : Prop) : (((A → A) → A) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_38_103 (A B C : Prop) : (((A → A) → B) → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_38_104 (A B : Prop) : (((A → A) → A) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_1 (A B C D E : Prop) : ((A → B → C) → D → E → E) := by
  run_tac tactic_name
theorem propfmls_5_39_2 (A B C D : Prop) : ((A → B → C) → D → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_3 (A B C D : Prop) : ((A → B → C) → A → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_4 (A B C D : Prop) : ((A → B → A) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_5 (A B C D : Prop) : ((A → A → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_6 (A B C D : Prop) : ((A → B → C) → D → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_7 (A B C : Prop) : ((A → A → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_8 (A B C : Prop) : ((A → B → C) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_9 (A B C : Prop) : ((A → B → A) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_10 (A B C D : Prop) : ((A → B → C) → B → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_11 (A B C : Prop) : ((A → B → C) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_12 (A B C : Prop) : ((A → A → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_13 (A B C : Prop) : ((A → B → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_14 (A B C D : Prop) : ((A → B → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_15 (A B C : Prop) : ((A → B → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_16 (A B C : Prop) : ((A → B → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_17 (A B C : Prop) : ((A → A → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_18 (A B C D : Prop) : ((A → B → C) → D → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_19 (A B C : Prop) : ((A → B → A) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_20 (A B C : Prop) : ((A → B → C) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_21 (A B C : Prop) : ((A → A → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_22 (A B C : Prop) : ((A → B → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_23 (A B : Prop) : ((A → A → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_24 (A B : Prop) : ((A → B → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_25 (A B C : Prop) : ((A → B → C) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_26 (A B : Prop) : ((A → B → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_27 (A B : Prop) : ((A → A → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_28 (A B C D : Prop) : ((A → B → C) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_29 (A B C : Prop) : ((A → B → C) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_30 (A B C : Prop) : ((A → B → A) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_31 (A B C : Prop) : ((A → A → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_32 (A B C : Prop) : ((A → B → C) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_33 (A B : Prop) : ((A → A → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_34 (A B : Prop) : ((A → B → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_35 (A B C : Prop) : ((A → B → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_36 (A B : Prop) : ((A → B → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_37 (A B : Prop) : ((A → A → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_38 (A B C D : Prop) : ((A → B → C) → D → D → D) := by
  run_tac tactic_name
theorem propfmls_5_39_39 (A B C : Prop) : ((A → B → C) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_40 (A B C : Prop) : ((A → B → A) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_41 (A B C : Prop) : ((A → A → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_42 (A B C : Prop) : ((A → B → C) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_43 (A B : Prop) : ((A → A → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_44 (A B : Prop) : ((A → B → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_45 (A B C : Prop) : ((A → B → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_46 (A B : Prop) : ((A → B → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_47 (A B : Prop) : ((A → A → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_48 (A B C : Prop) : ((A → B → C) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_39_49 (A B : Prop) : ((A → B → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_50 (A B : Prop) : ((A → A → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_51 (A B : Prop) : ((A → B → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_39_52 (A : Prop) : ((A → A → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_39_53 (A B C D E : Prop) : ((A → B → C) → D → E → D) := by
  run_tac tactic_name
theorem propfmls_5_39_54 (A B C D : Prop) : ((A → B → C) → A → D → A) := by
  run_tac tactic_name
theorem propfmls_5_39_55 (A B C D : Prop) : ((A → B → C) → D → A → D) := by
  run_tac tactic_name
theorem propfmls_5_39_56 (A B C D : Prop) : ((A → B → A) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_39_57 (A B C D : Prop) : ((A → A → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_39_58 (A B C D : Prop) : ((A → B → C) → B → D → B) := by
  run_tac tactic_name
theorem propfmls_5_39_59 (A B C : Prop) : ((A → A → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_39_60 (A B C : Prop) : ((A → B → C) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_61 (A B C : Prop) : ((A → B → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_39_62 (A B C D : Prop) : ((A → B → C) → D → B → D) := by
  run_tac tactic_name
theorem propfmls_5_39_63 (A B C : Prop) : ((A → B → C) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_64 (A B C : Prop) : ((A → A → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_39_65 (A B C : Prop) : ((A → B → A) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_39_66 (A B C D : Prop) : ((A → B → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_39_67 (A B C : Prop) : ((A → B → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_39_68 (A B C : Prop) : ((A → B → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_39_69 (A B C : Prop) : ((A → A → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_39_70 (A B C D : Prop) : ((A → B → C) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_39_71 (A B C : Prop) : ((A → B → A) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_39_72 (A B C : Prop) : ((A → B → C) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_39_73 (A B C : Prop) : ((A → A → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_39_74 (A B C : Prop) : ((A → B → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_39_75 (A B : Prop) : ((A → A → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_76 (A B : Prop) : ((A → B → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_77 (A B C : Prop) : ((A → B → C) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_39_78 (A B : Prop) : ((A → B → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_79 (A B : Prop) : ((A → A → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_80 (A B C D : Prop) : ((A → B → C) → D → C → D) := by
  run_tac tactic_name
theorem propfmls_5_39_81 (A B C : Prop) : ((A → B → C) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_39_82 (A B C : Prop) : ((A → B → A) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_39_83 (A B C : Prop) : ((A → A → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_39_84 (A B C : Prop) : ((A → B → C) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_39_85 (A B : Prop) : ((A → A → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_86 (A B : Prop) : ((A → B → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_87 (A B C : Prop) : ((A → B → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_39_88 (A B : Prop) : ((A → B → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_39_89 (A B : Prop) : ((A → A → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_90 (A B C : Prop) : ((A → A → B) → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_91 (A B : Prop) : ((A → A → B) → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_39_92 (A B C : Prop) : ((A → B → C) → A → B → C) := by
  run_tac tactic_name
theorem propfmls_5_39_93 (A B C : Prop) : ((A → B → C) → B → A → C) := by
  run_tac tactic_name
theorem propfmls_5_39_94 (A B C : Prop) : ((A → A → B) → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_1 (A B C D E : Prop) : (A → (B → C) → D → E → E) := by
  run_tac tactic_name
theorem propfmls_5_40_2 (A B C D : Prop) : (A → (B → C) → D → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_3 (A B C D : Prop) : (A → (B → C) → A → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_4 (A B C D : Prop) : (A → (B → A) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_5 (A B C D : Prop) : (A → (A → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_6 (A B C D : Prop) : (A → (B → C) → D → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_7 (A B C : Prop) : (A → (A → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_8 (A B C : Prop) : (A → (B → C) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_9 (A B C : Prop) : (A → (B → A) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_10 (A B C D : Prop) : (A → (B → C) → B → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_11 (A B C : Prop) : (A → (B → C) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_12 (A B C : Prop) : (A → (A → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_13 (A B C : Prop) : (A → (B → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_14 (A B C D : Prop) : (A → (B → B) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_15 (A B C : Prop) : (A → (B → B) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_16 (A B C : Prop) : (A → (B → B) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_17 (A B C : Prop) : (A → (A → A) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_18 (A B C D : Prop) : (A → (B → C) → D → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_19 (A B C : Prop) : (A → (B → A) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_20 (A B C : Prop) : (A → (B → C) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_21 (A B C : Prop) : (A → (A → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_22 (A B C : Prop) : (A → (B → B) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_23 (A B : Prop) : (A → (A → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_24 (A B : Prop) : (A → (B → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_25 (A B C : Prop) : (A → (B → C) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_26 (A B : Prop) : (A → (B → A) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_27 (A B : Prop) : (A → (A → B) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_28 (A B C D : Prop) : (A → (B → C) → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_29 (A B C : Prop) : (A → (B → C) → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_30 (A B C : Prop) : (A → (B → A) → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_31 (A B C : Prop) : (A → (A → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_32 (A B C : Prop) : (A → (B → C) → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_33 (A B : Prop) : (A → (A → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_34 (A B : Prop) : (A → (B → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_35 (A B C : Prop) : (A → (B → B) → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_36 (A B : Prop) : (A → (B → B) → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_37 (A B : Prop) : (A → (A → A) → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_38 (A B C D : Prop) : (A → (B → C) → D → D → D) := by
  run_tac tactic_name
theorem propfmls_5_40_39 (A B C : Prop) : (A → (B → C) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_40 (A B C : Prop) : (A → (B → A) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_41 (A B C : Prop) : (A → (A → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_42 (A B C : Prop) : (A → (B → C) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_43 (A B : Prop) : (A → (A → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_44 (A B : Prop) : (A → (B → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_45 (A B C : Prop) : (A → (B → B) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_46 (A B : Prop) : (A → (B → B) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_47 (A B : Prop) : (A → (A → A) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_48 (A B C : Prop) : (A → (B → C) → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_40_49 (A B : Prop) : (A → (B → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_50 (A B : Prop) : (A → (A → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_51 (A B : Prop) : (A → (B → B) → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_40_52 (A : Prop) : (A → (A → A) → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_40_53 (A B C D E : Prop) : (A → (B → C) → D → E → D) := by
  run_tac tactic_name
theorem propfmls_5_40_54 (A B C D : Prop) : (A → (B → C) → A → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_55 (A B C D : Prop) : (A → (B → C) → D → A → D) := by
  run_tac tactic_name
theorem propfmls_5_40_56 (A B C D : Prop) : (A → (B → A) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_40_57 (A B C D : Prop) : (A → (A → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_40_58 (A B C D : Prop) : (A → (B → C) → B → D → B) := by
  run_tac tactic_name
theorem propfmls_5_40_59 (A B C : Prop) : (A → (A → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_60 (A B C : Prop) : (A → (B → C) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_61 (A B C : Prop) : (A → (B → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_62 (A B C D : Prop) : (A → (B → C) → D → B → D) := by
  run_tac tactic_name
theorem propfmls_5_40_63 (A B C : Prop) : (A → (B → C) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_64 (A B C : Prop) : (A → (A → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_40_65 (A B C : Prop) : (A → (B → A) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_66 (A B C D : Prop) : (A → (B → B) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_40_67 (A B C : Prop) : (A → (B → B) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_68 (A B C : Prop) : (A → (B → B) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_40_69 (A B C : Prop) : (A → (A → A) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_70 (A B C D : Prop) : (A → (B → C) → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_40_71 (A B C : Prop) : (A → (B → A) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_72 (A B C : Prop) : (A → (B → C) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_40_73 (A B C : Prop) : (A → (A → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_74 (A B C : Prop) : (A → (B → B) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_75 (A B : Prop) : (A → (A → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_76 (A B : Prop) : (A → (B → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_77 (A B C : Prop) : (A → (B → C) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_78 (A B : Prop) : (A → (B → A) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_79 (A B : Prop) : (A → (A → B) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_80 (A B C D : Prop) : (A → (B → C) → D → C → D) := by
  run_tac tactic_name
theorem propfmls_5_40_81 (A B C : Prop) : (A → (B → C) → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_82 (A B C : Prop) : (A → (B → A) → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_40_83 (A B C : Prop) : (A → (A → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_84 (A B C : Prop) : (A → (B → C) → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_85 (A B : Prop) : (A → (A → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_86 (A B : Prop) : (A → (B → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_87 (A B C : Prop) : (A → (B → B) → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_88 (A B : Prop) : (A → (B → B) → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_89 (A B : Prop) : (A → (A → A) → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_90 (A B C D E : Prop) : (A → (B → C) → D → E → A) := by
  run_tac tactic_name
theorem propfmls_5_40_91 (A B C D : Prop) : (A → (A → B) → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_92 (A B C D : Prop) : (A → (B → C) → D → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_93 (A B C D : Prop) : (A → (B → C) → B → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_94 (A B C D : Prop) : (A → (B → B) → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_95 (A B C D : Prop) : (A → (B → A) → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_96 (A B C : Prop) : (A → (A → A) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_97 (A B C : Prop) : (A → (B → A) → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_98 (A B C : Prop) : (A → (B → A) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_99 (A B C D : Prop) : (A → (B → C) → D → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_100 (A B C : Prop) : (A → (A → B) → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_101 (A B C : Prop) : (A → (B → B) → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_102 (A B C : Prop) : (A → (B → C) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_103 (A B C D : Prop) : (A → (B → C) → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_104 (A B C : Prop) : (A → (A → B) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_105 (A B C : Prop) : (A → (B → C) → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_106 (A B C : Prop) : (A → (B → B) → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_107 (A B C D : Prop) : (A → (B → C) → D → D → A) := by
  run_tac tactic_name
theorem propfmls_5_40_108 (A B C : Prop) : (A → (A → B) → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_109 (A B C : Prop) : (A → (B → C) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_110 (A B C : Prop) : (A → (B → B) → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_111 (A B C : Prop) : (A → (B → A) → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_112 (A B : Prop) : (A → (A → A) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_113 (A B : Prop) : (A → (B → A) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_114 (A B C : Prop) : (A → (B → C) → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_40_115 (A B : Prop) : (A → (A → B) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_116 (A B : Prop) : (A → (B → B) → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_40_117 (A B C D : Prop) : (A → (B → C) → D → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_118 (A B C : Prop) : (A → (A → B) → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_119 (A B C : Prop) : (A → (B → C) → A → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_120 (A B C : Prop) : (A → (B → C) → B → B → C) := by
  run_tac tactic_name
theorem propfmls_5_40_121 (A B : Prop) : (A → (A → B) → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_40_122 (A B C D : Prop) : (A → (B → C) → B → D → C) := by
  run_tac tactic_name
theorem propfmls_5_40_123 (A B C : Prop) : (A → (B → C) → B → A → C) := by
  run_tac tactic_name
theorem propfmls_5_40_124 (A B C : Prop) : (A → (A → B) → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_40_125 (A B C D : Prop) : (A → (A → B) → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_40_126 (A B C : Prop) : (A → (A → B) → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_1 (A B C D E : Prop) : ((A → B) → C → D → E → E) := by
  run_tac tactic_name
theorem propfmls_5_41_2 (A B C D : Prop) : ((A → B) → C → D → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_3 (A B C D : Prop) : ((A → B) → C → A → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_4 (A B C D : Prop) : ((A → B) → A → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_5 (A B C D : Prop) : ((A → A) → B → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_6 (A B C D : Prop) : ((A → B) → C → D → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_7 (A B C : Prop) : ((A → A) → B → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_8 (A B C : Prop) : ((A → B) → C → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_9 (A B C : Prop) : ((A → B) → A → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_10 (A B C D : Prop) : ((A → B) → C → B → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_11 (A B C : Prop) : ((A → B) → C → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_12 (A B C : Prop) : ((A → A) → B → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_13 (A B C : Prop) : ((A → B) → A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_14 (A B C D : Prop) : ((A → B) → B → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_15 (A B C : Prop) : ((A → B) → B → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_16 (A B C : Prop) : ((A → B) → B → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_17 (A B C : Prop) : ((A → A) → A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_18 (A B C D : Prop) : ((A → B) → C → D → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_19 (A B C : Prop) : ((A → B) → A → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_20 (A B C : Prop) : ((A → B) → C → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_21 (A B C : Prop) : ((A → A) → B → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_22 (A B C : Prop) : ((A → B) → B → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_23 (A B : Prop) : ((A → A) → A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_24 (A B : Prop) : ((A → B) → B → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_25 (A B C : Prop) : ((A → B) → C → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_26 (A B : Prop) : ((A → B) → A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_27 (A B : Prop) : ((A → A) → B → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_28 (A B C D : Prop) : ((A → B) → C → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_29 (A B C : Prop) : ((A → B) → C → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_30 (A B C : Prop) : ((A → B) → A → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_31 (A B C : Prop) : ((A → A) → B → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_32 (A B C : Prop) : ((A → B) → C → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_33 (A B : Prop) : ((A → A) → B → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_34 (A B : Prop) : ((A → B) → A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_35 (A B C : Prop) : ((A → B) → B → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_36 (A B : Prop) : ((A → B) → B → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_37 (A B : Prop) : ((A → A) → A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_38 (A B C D : Prop) : ((A → B) → C → D → D → D) := by
  run_tac tactic_name
theorem propfmls_5_41_39 (A B C : Prop) : ((A → B) → C → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_40 (A B C : Prop) : ((A → B) → A → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_41 (A B C : Prop) : ((A → A) → B → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_42 (A B C : Prop) : ((A → B) → C → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_43 (A B : Prop) : ((A → A) → B → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_44 (A B : Prop) : ((A → B) → A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_45 (A B C : Prop) : ((A → B) → B → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_46 (A B : Prop) : ((A → B) → B → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_47 (A B : Prop) : ((A → A) → A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_48 (A B C : Prop) : ((A → B) → C → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_41_49 (A B : Prop) : ((A → B) → A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_50 (A B : Prop) : ((A → A) → B → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_51 (A B : Prop) : ((A → B) → B → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_41_52 (A : Prop) : ((A → A) → A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_41_53 (A B C D E : Prop) : ((A → B) → C → D → E → D) := by
  run_tac tactic_name
theorem propfmls_5_41_54 (A B C D : Prop) : ((A → B) → C → A → D → A) := by
  run_tac tactic_name
theorem propfmls_5_41_55 (A B C D : Prop) : ((A → B) → C → D → A → D) := by
  run_tac tactic_name
theorem propfmls_5_41_56 (A B C D : Prop) : ((A → B) → A → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_57 (A B C D : Prop) : ((A → A) → B → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_58 (A B C D : Prop) : ((A → B) → C → B → D → B) := by
  run_tac tactic_name
theorem propfmls_5_41_59 (A B C : Prop) : ((A → A) → B → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_60 (A B C : Prop) : ((A → B) → C → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_61 (A B C : Prop) : ((A → B) → A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_62 (A B C D : Prop) : ((A → B) → C → D → B → D) := by
  run_tac tactic_name
theorem propfmls_5_41_63 (A B C : Prop) : ((A → B) → C → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_64 (A B C : Prop) : ((A → A) → B → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_65 (A B C : Prop) : ((A → B) → A → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_66 (A B C D : Prop) : ((A → B) → B → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_67 (A B C : Prop) : ((A → B) → B → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_68 (A B C : Prop) : ((A → B) → B → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_69 (A B C : Prop) : ((A → A) → A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_70 (A B C D : Prop) : ((A → B) → C → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_71 (A B C : Prop) : ((A → B) → A → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_72 (A B C : Prop) : ((A → B) → C → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_73 (A B C : Prop) : ((A → A) → B → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_74 (A B C : Prop) : ((A → B) → B → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_75 (A B : Prop) : ((A → A) → A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_76 (A B : Prop) : ((A → B) → B → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_77 (A B C : Prop) : ((A → B) → C → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_78 (A B : Prop) : ((A → B) → A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_79 (A B : Prop) : ((A → A) → B → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_80 (A B C D : Prop) : ((A → B) → C → D → C → D) := by
  run_tac tactic_name
theorem propfmls_5_41_81 (A B C : Prop) : ((A → B) → C → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_82 (A B C : Prop) : ((A → B) → A → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_83 (A B C : Prop) : ((A → A) → B → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_84 (A B C : Prop) : ((A → B) → C → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_85 (A B : Prop) : ((A → A) → B → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_86 (A B : Prop) : ((A → B) → A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_87 (A B C : Prop) : ((A → B) → B → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_88 (A B : Prop) : ((A → B) → B → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_89 (A B : Prop) : ((A → A) → A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_90 (A B C D E : Prop) : ((A → B) → C → D → E → C) := by
  run_tac tactic_name
theorem propfmls_5_41_91 (A B C D : Prop) : ((A → B) → A → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_41_92 (A B C D : Prop) : ((A → B) → C → D → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_93 (A B C D : Prop) : ((A → B) → C → A → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_94 (A B C D : Prop) : ((A → A) → B → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_41_95 (A B C D : Prop) : ((A → B) → B → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_41_96 (A B C : Prop) : ((A → A) → A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_97 (A B C : Prop) : ((A → B) → B → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_98 (A B C : Prop) : ((A → B) → B → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_99 (A B C D : Prop) : ((A → B) → C → D → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_100 (A B C : Prop) : ((A → B) → A → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_101 (A B C : Prop) : ((A → A) → B → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_102 (A B C : Prop) : ((A → B) → C → A → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_103 (A B C D : Prop) : ((A → B) → C → B → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_104 (A B C : Prop) : ((A → B) → A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_105 (A B C : Prop) : ((A → B) → C → B → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_106 (A B C : Prop) : ((A → A) → B → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_107 (A B C D : Prop) : ((A → B) → C → D → D → C) := by
  run_tac tactic_name
theorem propfmls_5_41_108 (A B C : Prop) : ((A → B) → A → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_41_109 (A B C : Prop) : ((A → B) → C → A → A → C) := by
  run_tac tactic_name
theorem propfmls_5_41_110 (A B C : Prop) : ((A → A) → B → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_111 (A B C : Prop) : ((A → B) → B → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_112 (A B : Prop) : ((A → A) → A → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_113 (A B : Prop) : ((A → B) → B → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_114 (A B C : Prop) : ((A → B) → C → B → B → C) := by
  run_tac tactic_name
theorem propfmls_5_41_115 (A B : Prop) : ((A → B) → A → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_41_116 (A B : Prop) : ((A → A) → B → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_117 (A B C D : Prop) : ((A → B) → C → D → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_118 (A B C : Prop) : ((A → B) → A → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_119 (A B C : Prop) : ((A → B) → C → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_120 (A B C : Prop) : ((A → B) → C → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_121 (A B : Prop) : ((A → B) → A → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_41_122 (A B C D : Prop) : ((A → B) → C → A → D → B) := by
  run_tac tactic_name
theorem propfmls_5_41_123 (A B C : Prop) : ((A → B) → C → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_124 (A B C : Prop) : ((A → B) → A → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_41_125 (A B C D : Prop) : ((A → B) → A → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_41_126 (A B C : Prop) : ((A → B) → A → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_1 (A B C D E : Prop) : (A → B → C → D → E → E) := by
  run_tac tactic_name
theorem propfmls_5_42_2 (A B C D : Prop) : (A → B → C → D → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_3 (A B C D : Prop) : (A → B → C → A → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_4 (A B C D : Prop) : (A → B → A → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_5 (A B C D : Prop) : (A → A → B → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_6 (A B C D : Prop) : (A → B → C → D → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_7 (A B C : Prop) : (A → A → B → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_8 (A B C : Prop) : (A → B → C → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_9 (A B C : Prop) : (A → B → A → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_10 (A B C D : Prop) : (A → B → C → B → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_11 (A B C : Prop) : (A → B → C → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_12 (A B C : Prop) : (A → A → B → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_13 (A B C : Prop) : (A → B → A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_14 (A B C D : Prop) : (A → B → B → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_15 (A B C : Prop) : (A → B → B → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_16 (A B C : Prop) : (A → B → B → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_17 (A B C : Prop) : (A → A → A → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_18 (A B C D : Prop) : (A → B → C → D → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_19 (A B C : Prop) : (A → B → A → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_20 (A B C : Prop) : (A → B → C → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_21 (A B C : Prop) : (A → A → B → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_22 (A B C : Prop) : (A → B → B → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_23 (A B : Prop) : (A → A → A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_24 (A B : Prop) : (A → B → B → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_25 (A B C : Prop) : (A → B → C → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_26 (A B : Prop) : (A → B → A → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_27 (A B : Prop) : (A → A → B → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_28 (A B C D : Prop) : (A → B → C → C → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_29 (A B C : Prop) : (A → B → C → C → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_30 (A B C : Prop) : (A → B → A → A → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_31 (A B C : Prop) : (A → A → B → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_32 (A B C : Prop) : (A → B → C → C → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_33 (A B : Prop) : (A → A → B → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_34 (A B : Prop) : (A → B → A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_35 (A B C : Prop) : (A → B → B → B → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_36 (A B : Prop) : (A → B → B → B → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_37 (A B : Prop) : (A → A → A → A → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_38 (A B C D : Prop) : (A → B → C → D → D → D) := by
  run_tac tactic_name
theorem propfmls_5_42_39 (A B C : Prop) : (A → B → C → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_40 (A B C : Prop) : (A → B → A → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_41 (A B C : Prop) : (A → A → B → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_42 (A B C : Prop) : (A → B → C → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_43 (A B : Prop) : (A → A → B → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_44 (A B : Prop) : (A → B → A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_45 (A B C : Prop) : (A → B → B → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_46 (A B : Prop) : (A → B → B → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_47 (A B : Prop) : (A → A → A → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_48 (A B C : Prop) : (A → B → C → C → C → C) := by
  run_tac tactic_name
theorem propfmls_5_42_49 (A B : Prop) : (A → B → A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_50 (A B : Prop) : (A → A → B → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_51 (A B : Prop) : (A → B → B → B → B → B) := by
  run_tac tactic_name
theorem propfmls_5_42_52 (A : Prop) : (A → A → A → A → A → A) := by
  run_tac tactic_name
theorem propfmls_5_42_53 (A B C D E : Prop) : (A → B → C → D → E → D) := by
  run_tac tactic_name
theorem propfmls_5_42_54 (A B C D : Prop) : (A → B → C → A → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_55 (A B C D : Prop) : (A → B → C → D → A → D) := by
  run_tac tactic_name
theorem propfmls_5_42_56 (A B C D : Prop) : (A → B → A → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_57 (A B C D : Prop) : (A → A → B → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_58 (A B C D : Prop) : (A → B → C → B → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_59 (A B C : Prop) : (A → A → B → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_60 (A B C : Prop) : (A → B → C → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_61 (A B C : Prop) : (A → B → A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_62 (A B C D : Prop) : (A → B → C → D → B → D) := by
  run_tac tactic_name
theorem propfmls_5_42_63 (A B C : Prop) : (A → B → C → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_64 (A B C : Prop) : (A → A → B → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_65 (A B C : Prop) : (A → B → A → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_66 (A B C D : Prop) : (A → B → B → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_67 (A B C : Prop) : (A → B → B → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_68 (A B C : Prop) : (A → B → B → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_69 (A B C : Prop) : (A → A → A → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_70 (A B C D : Prop) : (A → B → C → C → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_71 (A B C : Prop) : (A → B → A → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_72 (A B C : Prop) : (A → B → C → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_73 (A B C : Prop) : (A → A → B → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_74 (A B C : Prop) : (A → B → B → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_75 (A B : Prop) : (A → A → A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_76 (A B : Prop) : (A → B → B → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_77 (A B C : Prop) : (A → B → C → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_78 (A B : Prop) : (A → B → A → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_79 (A B : Prop) : (A → A → B → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_80 (A B C D : Prop) : (A → B → C → D → C → D) := by
  run_tac tactic_name
theorem propfmls_5_42_81 (A B C : Prop) : (A → B → C → A → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_82 (A B C : Prop) : (A → B → A → C → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_83 (A B C : Prop) : (A → A → B → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_84 (A B C : Prop) : (A → B → C → B → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_85 (A B : Prop) : (A → A → B → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_86 (A B : Prop) : (A → B → A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_87 (A B C : Prop) : (A → B → B → C → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_88 (A B : Prop) : (A → B → B → A → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_89 (A B : Prop) : (A → A → A → B → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_90 (A B C D E : Prop) : (A → B → C → D → E → C) := by
  run_tac tactic_name
theorem propfmls_5_42_91 (A B C D : Prop) : (A → B → A → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_92 (A B C D : Prop) : (A → B → C → D → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_93 (A B C D : Prop) : (A → B → C → A → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_94 (A B C D : Prop) : (A → A → B → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_95 (A B C D : Prop) : (A → B → B → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_96 (A B C : Prop) : (A → A → A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_97 (A B C : Prop) : (A → B → B → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_98 (A B C : Prop) : (A → B → B → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_99 (A B C D : Prop) : (A → B → C → D → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_100 (A B C : Prop) : (A → B → A → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_101 (A B C : Prop) : (A → A → B → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_102 (A B C : Prop) : (A → B → C → A → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_103 (A B C D : Prop) : (A → B → C → B → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_104 (A B C : Prop) : (A → B → A → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_105 (A B C : Prop) : (A → B → C → B → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_106 (A B C : Prop) : (A → A → B → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_107 (A B C D : Prop) : (A → B → C → D → D → C) := by
  run_tac tactic_name
theorem propfmls_5_42_108 (A B C : Prop) : (A → B → A → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_109 (A B C : Prop) : (A → B → C → A → A → C) := by
  run_tac tactic_name
theorem propfmls_5_42_110 (A B C : Prop) : (A → A → B → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_111 (A B C : Prop) : (A → B → B → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_112 (A B : Prop) : (A → A → A → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_113 (A B : Prop) : (A → B → B → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_114 (A B C : Prop) : (A → B → C → B → B → C) := by
  run_tac tactic_name
theorem propfmls_5_42_115 (A B : Prop) : (A → B → A → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_116 (A B : Prop) : (A → A → B → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_117 (A B C D E : Prop) : (A → B → C → D → E → B) := by
  run_tac tactic_name
theorem propfmls_5_42_118 (A B C D : Prop) : (A → A → B → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_119 (A B C D : Prop) : (A → B → C → D → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_120 (A B C D : Prop) : (A → B → C → A → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_121 (A B C D : Prop) : (A → B → A → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_122 (A B C D : Prop) : (A → B → C → D → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_123 (A B C : Prop) : (A → A → B → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_124 (A B C : Prop) : (A → B → A → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_125 (A B C : Prop) : (A → B → C → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_126 (A B C D : Prop) : (A → B → C → C → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_127 (A B C : Prop) : (A → A → B → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_128 (A B C : Prop) : (A → B → C → C → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_129 (A B C : Prop) : (A → B → A → A → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_130 (A B C D : Prop) : (A → B → C → D → D → B) := by
  run_tac tactic_name
theorem propfmls_5_42_131 (A B C : Prop) : (A → A → B → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_132 (A B C : Prop) : (A → B → C → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_133 (A B C : Prop) : (A → B → A → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_134 (A B C : Prop) : (A → B → C → C → C → B) := by
  run_tac tactic_name
theorem propfmls_5_42_135 (A B : Prop) : (A → A → B → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_136 (A B : Prop) : (A → B → A → A → A → B) := by
  run_tac tactic_name
theorem propfmls_5_42_137 (A B C D E : Prop) : (A → B → C → D → E → A) := by
  run_tac tactic_name
theorem propfmls_5_42_138 (A B C D : Prop) : (A → B → C → D → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_139 (A B C D : Prop) : (A → B → C → B → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_140 (A B C D : Prop) : (A → B → B → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_141 (A B C D : Prop) : (A → B → C → D → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_142 (A B C : Prop) : (A → B → B → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_143 (A B C : Prop) : (A → B → C → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_144 (A B C D : Prop) : (A → B → C → C → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_145 (A B C : Prop) : (A → B → C → C → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_146 (A B C : Prop) : (A → B → B → B → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_147 (A B C D : Prop) : (A → B → C → D → D → A) := by
  run_tac tactic_name
theorem propfmls_5_42_148 (A B C : Prop) : (A → B → C → B → B → A) := by
  run_tac tactic_name
theorem propfmls_5_42_149 (A B C : Prop) : (A → B → B → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_150 (A B C : Prop) : (A → B → C → C → C → A) := by
  run_tac tactic_name
theorem propfmls_5_42_151 (A B : Prop) : (A → B → B → B → B → A) := by
  run_tac tactic_name
