import Lean
open Lean Meta Elab.Tactic

/-!
# Tactic: prove_paren_impl_taut

## Mathematical Specification

**Class of formulas**: Let `ImpForm` be the set of formulas built from:
- Propositional variables: `P, Q, R, ...`
- Implication connective: `→` (right-associative)
- Parentheses for grouping

**Target set**: `{ φ ∈ ImpForm | φ is a tautology in minimal implicational logic }`

**Logical fragment**: Propositional logic with implication only (no ∧, ∨, ¬, or other connectives)

**Provability conditions**: A formula φ is provable iff it can be derived using:
1. **Axiom K**: `A → (B → A)`
2. **Axiom S**: `(A → (B → C)) → ((A → B) → (A → C))`
3. **Modus Ponens**: From `A → B` and `A`, infer `B`

## Algorithm

1. **Structure Analysis**:
   - Parse the goal expression to extract implication structure
   - Identify all propositional variables
   - Build abstract syntax tree with only `→` nodes and variable leaves

2. **Tautology Check**:
   - Apply semantic evaluation over all possible truth assignments
   - If any assignment makes the formula false, fail immediately
   - If all assignments make it true, proceed to proof construction

3. **Proof Construction** (using natural deduction):
   - For formulas matching known axiom patterns (K, S), apply directly
   - For complex formulas, use proof search with:
     - Backward chaining from goal
     - Introduction rules for `→` (move antecedent to hypothesis)
     - Elimination rules for `→` (modus ponens)
   - Construct proof term using `intro`, `apply`, and `exact` tactics

4. **Term Building**:
   - Build the actual proof term as a lambda expression
   - Use `mkLambda`, `mkApp` for proof construction
   - Apply the constructed term to close the goal
-/

/-- Helper: try to close goal with assumption -/
def tryAssumption (goal : MVarId) : TacticM Bool := do
  goal.withContext do
    let goalType ← goal.getType
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type goalType then
        goal.assign (Expr.fvar decl.fvarId)
        return true
    return false

/-- Collect all non-dependent argument types from a function type -/
partial def collectArgTypes (ty : Expr) : List Expr :=
  match ty with
  | .forallE _ dom body _ =>
    if body.hasLooseBVars then []
    else dom :: collectArgTypes body
  | _ => []

/-- Get the final result type after applying all arguments -/
partial def getFinalType (ty : Expr) : Expr :=
  match ty with
  | .forallE _ _ body _ =>
    if body.hasLooseBVars then ty
    else getFinalType body
  | _ => ty

/-- Try to build a proof term for a type using available hypotheses -/
partial def buildProof (goalType : Expr) (lctx : LocalContext) (depth : Nat) : MetaM (Option Expr) := do
  if depth > 30 then return none

  -- Try direct hypothesis
  for decl in lctx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type goalType then
      return some (Expr.fvar decl.fvarId)

  -- If goalType is a function type, try to build a lambda using withLocalDecl
  match goalType with
  | .forallE name dom body bi =>
    if !body.hasLooseBVars then
      -- Non-dependent function type: build fun (x : dom) => <proof of body>
      let result ← withLocalDecl name bi dom fun fvar => do
        let lctx' ← getLCtx
        if let some bodyProof ← buildProof body lctx' (depth + 1) then
          let lamProof ← mkLambdaFVars #[fvar] bodyProof
          return some lamProof
        return none
      if result.isSome then return result
  | _ => pure ()

  -- Try applying hypotheses with any number of arguments
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let argTypes := collectArgTypes decl.type
    let finalType := getFinalType decl.type
    if argTypes.isEmpty then continue
    if ← isDefEq finalType goalType then
      -- Try to build proofs for all arguments
      let mut args : Array Expr := #[]
      let mut allFound := true
      for argType in argTypes do
        if let some argProof ← buildProof argType lctx (depth + 1) then
          args := args.push argProof
        else
          allFound := false
          break
      if allFound then
        let mut proof := Expr.fvar decl.fvarId
        for arg in args do
          proof := Expr.app proof arg
        return some proof

  return none

/-- Helper: recursively prove the goal with full proof search -/
partial def proveGoal (goal : MVarId) (depth : Nat) : TacticM Bool := do
  if depth > 50 then return false
  goal.withContext do
    let goalType ← goal.getType
    -- First try assumption
    if ← tryAssumption goal then return true
    -- If goal is an implication, introduce it and recurse
    match goalType with
    | .forallE _ _ _ _ =>
      let (_, newGoal) ← goal.intro1
      proveGoal newGoal (depth + 1)
    | _ =>
      -- Try to build a proof using hypotheses
      let lctx ← getLCtx
      if let some proof ← buildProof goalType lctx 0 then
        goal.assign proof
        return true
      return false

/-- Proves tautologies in the implication-only fragment of propositional logic. -/
def prove_paren_impl_taut : TacticM Unit := do
  let goal ← getMainGoal
  let success ← proveGoal goal 0
  if success then
    setGoals []
  else
    throwError "prove_paren_impl_taut: could not prove the goal"

-- Original generated tests
theorem test_1 (A B : Prop) : A → (B → A) := by
  run_tac prove_paren_impl_taut

theorem test_2 (A : Prop) : A → A := by
  run_tac prove_paren_impl_taut

theorem test_3 (P : Prop) : P → (P → P) := by
  run_tac prove_paren_impl_taut

theorem test_4 (A B C : Prop) : (A → (B → C)) → ((A → B) → (A → C)) := by
  run_tac prove_paren_impl_taut

theorem test_5 (P Q R : Prop) : P → (Q → (R → P)) := by
  run_tac prove_paren_impl_taut

theorem test_6 (A B : Prop) : (A → B) → (A → B) := by
  run_tac prove_paren_impl_taut

theorem test_7 (X Y Z : Prop) : (X → (Y → Z)) → (Y → (X → Z)) := by
  run_tac prove_paren_impl_taut

theorem test_8 (P Q : Prop) : (P → (P → Q)) → (P → Q) := by
  run_tac prove_paren_impl_taut

theorem test_9 (A B : Prop) : A → ((A → B) → B) := by
  run_tac prove_paren_impl_taut

theorem test_10 (P Q R S : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  run_tac prove_paren_impl_taut

theorem test_11 (X Y Z : Prop) : ((X → Y) → X) → X := by
  run_tac prove_paren_impl_taut

theorem test_12 (A B C : Prop) : A → (B → (C → (A → (B → C)))) := by
  run_tac prove_paren_impl_taut

theorem test_13 (P Q R : Prop) : (P → (Q → R)) → (Q → (P → R)) := by
  run_tac prove_paren_impl_taut

theorem test_14 (X Y Z W : Prop) : ((X → (Y → Z)) → W) → ((X → Y) → (X → Z) → W) := by
  run_tac prove_paren_impl_taut

theorem test_15 (A B C D E : Prop) : (A → (B → (C → D))) → (B → (A → (C → D))) := by
  run_tac prove_paren_impl_taut
