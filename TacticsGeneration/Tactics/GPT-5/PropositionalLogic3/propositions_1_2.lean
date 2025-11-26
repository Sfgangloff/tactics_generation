import Lean

open Lean Meta Elab Tactic
open Std

/-- A simple `run_tac` syntax: `run_tac t` is just expanded to `t`. -/
syntax (name := runTac) "run_tac" ident : tactic

macro_rules
  | `(tactic| run_tac $id) => `(tactic| $id)

/-- Our own small alias for sets of free-variable identifiers. -/
abbrev FVarSet := HashSet FVarId

/--
  Decompose a (non-dependent) function type `A₁ → … → Aₙ → R`
  into the list of argument types and the result type.
-/
partial def collectForallArgs (ty : Expr)
    (acc : Array Expr := #[]) : MetaM (Array Expr × Expr) := do
  let ty ← whnf ty
  match ty with
  | Expr.forallE _ dom body _ =>
      if body.hasLooseBVar 0 then
        -- dependent binder: stop peeling
        pure (acc, ty)
      else
        collectForallArgs body (acc.push dom)
  | _ =>
      pure (acc, ty)

/-!
We use mutual recursion between:

* `buildProof env goal blocked` : constructs a term of type `goal`
  using only implications and variables in `env`, forbidding the
  variables in `blocked` as *heads* of applications (to avoid self-loops).

* `buildArgs env tys i blocked acc` : builds arguments for a function
  of type `tys[i]` … → `tys[sz-1]` → result.

* `tryFuncs env goal blocked i` : tries to use hypotheses in `env`
  (from index `i`) whose type is of shape `A₁ → … → Aₙ → goal`.
-/
mutual

  /-- Main proof search in the implicational fragment. -/
  partial def buildProof (env : Array Expr) (goal : Expr)
      (blocked : FVarSet := {}) : MetaM Expr := do
    let goal ← whnf goal
    match goal with
    | Expr.forallE n dom body bi =>
        -- Treat non-dependent ∀ as implication.
        if body.hasLooseBVar 0 then
          throwError "tactic_name: dependent function types not supported: {goal}"
        else
          withLocalDecl n bi dom fun x => do
            let env'  := env.push (mkFVar x)
            let body' := body.instantiate1 (mkFVar x)
            let pr ← buildProof env' body' blocked
            pure <| Expr.lam n dom pr bi

    | _ =>
        -- Atomic goal.
        -- Step 1: exact variable of same type, if any.
        let rec findExact (i : Nat) : MetaM (Option Expr) := do
          if h : i < env.size then
            let v := env[i]
            match v.fvarId? with
            | some fid =>
                if blocked.contains fid then
                  findExact (i+1)
                else
                  let vTy ← inferType v
                  if ← isDefEq vTy goal then
                    pure (some v)
                  else
                    findExact (i+1)
            | none =>
                findExact (i+1)
          else
            pure none

        match ← findExact 0 with
        | some v => pure v
        | none =>
          -- Step 2: use a function hypothesis A₁ → … → Aₙ → goal.
          match ← tryFuncs env goal blocked 0 with
          | some t => pure t
          | none   => throwError "tactic_name: could not construct proof for goal {goal}."

  /-- Try to build arguments for a chain of types `tys`. -/
  partial def buildArgs (env : Array Expr) (tys : Array Expr) (i : Nat)
      (blocked : FVarSet) (acc : Array Expr) :
      MetaM (Option (Array Expr)) := do
    if h : i < tys.size then
      let ty := tys[i]
      -- try to build a proof of `ty`
      let res : Option Expr ←
        (try
          let pr ← buildProof env ty blocked
          pure (some pr)
        catch _ =>
          pure none)
      match res with
      | some arg =>
          buildArgs env tys (i+1) blocked (acc.push arg)
      | none =>
          pure none
    else
      pure (some acc)

  /-- Try to use a hypothesis `f` in `env` to reach `goal`. -/
  partial def tryFuncs (env : Array Expr) (goal : Expr)
      (blocked : FVarSet) (i : Nat) :
      MetaM (Option Expr) := do
    if h : i < env.size then
      let f := env[i]
      match f.fvarId? with
      | some fid =>
          if blocked.contains fid then
            tryFuncs env goal blocked (i+1)
          else
            let fTy ← inferType f
            let (argTys, resTy) ← collectForallArgs fTy
            if argTys.size = 0 then
              -- constant, skip
              tryFuncs env goal blocked (i+1)
            else if !(← isDefEq resTy goal) then
              tryFuncs env goal blocked (i+1)
            else
              -- f : A₁ → … → Aₙ → goal
              let blocked' := blocked.insert fid
              match ← buildArgs env argTys 0 blocked' #[] with
              | none =>
                  tryFuncs env goal blocked (i+1)
              | some args =>
                  -- build application f a₁ … aₙ
                  let mut app := f
                  for a in args do
                    app := Expr.app app a
                  pure (some app)
      | none =>
          tryFuncs env goal blocked (i+1)
    else
      pure none

end

/-- Tactic entry point to be used as `run_tac tactic_name`. -/
def tactic_name : TacticM Unit := do
  let g ← getMainGoal
  let proof? ← g.withContext do
    let t ← g.getType
    (try
      let pr ← buildProof #[] t {}
      pure (some pr)
    catch _ =>
      pure none)
  match proof? with
  | some pr =>
      g.assign pr
      setGoals []
  | none =>
      throwError "tactic_name failed on this goal."

/-! ### Examples: parenthesised implication tautologies -/

theorem propfmls_4_2_1 (A B C : Prop) :
    (((A → B → B) → C) → C) := by
  run_tac tactic_name

theorem propfmls_4_2_2 (A B C : Prop) :
    (A → B → C) → (A → B) → A → C := by
  run_tac tactic_name

theorem propfmls_4_2_3 (A B : Prop) :
    (A → B → A) := by
  run_tac tactic_name

theorem propfmls_4_2_4 (A B C : Prop) :
    (((A → B) → C) → (A → B) → C) := by
  run_tac tactic_name

theorem propfmls_4_2_5 (A : Prop) :
    A → A := by
  run_tac tactic_name
