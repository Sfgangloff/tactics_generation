import Lean
open Lean Meta Elab Tactic

/-- Canonical inhabitant for two-argument projections:
    `A → B → B`  and  `A → B → A`  (covers `A → A → A`). -/
private def mkProj2 (P : Expr) : MetaM (Option Expr) := do
  let P' ← whnf P
  match P' with
  | Expr.forallE _ A tail _ =>
    let tail' ← whnf tail
    match tail' with
    | Expr.forallE _ B body _ =>
      if (← isDefEq body B) then
        withLocalDecl `a .default A fun a => do
        withLocalDecl `b .default B fun b => do
          some <$> mkLambdaFVars #[a, b] b          -- λ a b, b
      else if (← isDefEq body A) then
        withLocalDecl `a .default A fun a => do
        withLocalDecl `b .default B fun b => do
          some <$> mkLambdaFVars #[a, b] a          -- λ a b, a
      else
        return none
    | _ => return none
  | _ => return none

/-- Build a one-argument arrow `U → V`.
    If `V ≡ U`, return identity; else if some local `e : V` exists, return the constant `λ _ : U => e`. -/
private def mkArrow1 (P : Expr) (locals : Array Expr) : MetaM (Option Expr) := do
  let P' ← whnf P
  match P' with
  | Expr.forallE _ U V _ =>
    let V' ← whnf V
    if (← isDefEq V' U) then
      withLocalDecl `x .default U fun x => some <$> mkLambdaFVars #[x] x
    else
      let mut found : Option Expr := none
      for e in locals do
        if found.isNone then
          if (← isDefEq (← inferType e) V') then
            let lam ← withLocalDecl `x .default U fun x => mkLambdaFVars #[x] e
            found := some lam
      return found
  | _ => return none

/-- Try to close a single subgoal `sg` from `locals`, or by synthesizing an inhabitant. -/
private def closeOne (sg : MVarId) (locals : Array Expr) : MetaM Bool := do
  let need ← sg.getType
  -- by a local
  for e in locals do
    if (← isDefEq (← inferType e) need) then
      sg.assign e
      return true
  -- or by synthesis
  if let some p ← mkProj2 need then
    sg.assign p
    return true
  if let some p ← mkArrow1 need locals then
    sg.assign p
    return true
  return false

/-- Introduce all arrows/foralls; then
    (1) close by exact if a fresh local matches the target;
    (2) otherwise, try `apply h : X₁ → … → Xₙ → tgt` for a local `h`,
        and attempt to close **each** generated subgoal `⊢ Xᵢ` with `closeOne`. -/
def intro_all_then_assumption : TacticM Unit := do
  let g0 ← getMainGoal
  let (fs, g) ← g0.intros
  replaceMainGoal [g]
  withMainContext do
    let locals : Array Expr := fs.map mkFVar
    let tgt ← g.getType

    -- (1) exact match
    for e in locals do
      if (← isDefEq (← inferType e) tgt) then
        g.assign e
        setGoals []
        return

    -- (2) try applying any local function and close *all* subgoals
    for h in locals do
      if (← whnf (← inferType h)).isForall then
        let s ← saveState
        try
          let subs ← g.apply h
          let mut ok := true
          for sg in subs do
            if !(← closeOne sg locals) then
              ok := false
              break
          if ok then
            setGoals []
            return
          else
            s.restore
        catch _ =>
          s.restore

    throwError "intro_all_then_assumption: no introduced hypothesis matches the goal"

elab "intro_all_then_assumption" : tactic => intro_all_then_assumption

/-- Example stays unchanged and works with `run_tac`. -/
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
