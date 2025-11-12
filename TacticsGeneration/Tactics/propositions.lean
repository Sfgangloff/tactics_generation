import Lean
open Lean Meta Elab.Tactic

/-- Close a goal of the form `A → B → A` or `A → B → B` (and also `A → A → A`). -/
def proj_or_swap : TacticM Unit := do
  -- 1) Introduce two arguments `a` and `b`
  let g0 ← getMainGoal
  let (_, g1) ← g0.intro `a
  let (_, g2) ← g1.intro `b
  replaceMainGoal [g2]        -- make `g2` the active goal

  -- 2) Work in the current goal’s context
  withMainContext do
    let goal ← getMainGoal
    let ctx ← getLCtx
    let some da := ctx.findFromUserName? `a
      | throwError "internal error: could not find `a`"
    let some db := ctx.findFromUserName? `b
      | throwError "internal error: could not find `b`"
    let ea : Expr := .fvar da.fvarId
    let eb : Expr := .fvar db.fvarId

    -- 3) Choose the local whose type matches the goal and assign it
    let tgt ← goal.getType
    let ta  ← inferType ea
    if (← isDefEq ta tgt) then
      goal.assign ea           -- goal is `A`, solve using `a`
    else
      let tb ← inferType eb
      if (← isDefEq tb tgt) then
        goal.assign eb         -- goal is `B`, solve using `b`
      else
        throwError "neither `a` nor `b` matches the goal"

  -- 4) Done
  replaceMainGoal []

-- Same code works for all three
theorem propfmls_2_2_1 (A B : Prop) : (A → B → B) := by
  run_tac proj_or_swap

theorem propfmls_2_2_2 (A : Prop) : (A → A → A) := by
  run_tac proj_or_swap

theorem propfmls_2_2_3 (A B : Prop) : (A → B → A) := by
  run_tac proj_or_swap
