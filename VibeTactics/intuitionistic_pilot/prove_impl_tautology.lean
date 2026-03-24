import Lean
open Lean Meta Elab.Tactic

/-!
# Tactic: prove_impl_tautology

## Mathematical Specification

**Formula class**: Formulas in the implication fragment of intuitionistic propositional logic:
F ::= P | F₁ → F₂
where P ranges over atomic propositions (in Lean: `Prop` variables).

**Logical fragment**: Intuitionistic propositional logic restricted to implication (→) only.

**Precise provability conditions**: A formula φ is provable by this tactic if:
1. φ is built only from atomic propositions and implication
2. φ is intuitionistically valid 
3. A proof of φ can be constructed using the following restricted proof search:
   - Repeatedly apply implication introduction (moving antecedents to context)
   - Use assumptions directly when they match the goal
   - Apply modus ponens when an assumption has the form A → B and we can prove A

**Target formula structure**: Formulas of the form:
{φ | φ ∈ ImplFormulas ∧ ⊢ᵢ φ ∧ ProofFoundByForwardChaining(φ)}

## Algorithm

1. **Structure Analysis**: Parse the goal to verify it contains only implications and atomic propositions
2. **Normalization**: Convert goal to normal form by repeatedly applying implication introduction, moving all antecedents to the context
3. **Context Building**: Collect all available hypotheses (both from original context and newly introduced assumptions)
4. **Goal Matching**: 
   - If goal is atomic, search for exact match in context
   - If goal is atomic, search for implications in context that conclude the goal
5. **Forward Chaining**: For each implication `A → B` in context:
   - If we can prove `A` (recursively), then we have `B`
   - Add `B` to our derived facts
6. **Proof Construction**: Build the actual proof term using:
   - `fun x => ...` for implication introduction  
   - Function application for modus ponens
   - Direct hypothesis reference for axioms
-/

/-- Prove intuitionistic tautologies built from implications using systematic application of introduction and elimination rules. -/
def prove_impl_tautology : TacticM Unit := do
  -- Check if expression contains only implications and atomic propositions
  partial def isImplOnly (e : Expr) : Bool :=
    match e with
    | Expr.forallE _ _ body _ => isImplOnly body
    | Expr.app (Expr.app (Expr.const ``Function.comp _) _) _ => false
    | Expr.app _ _ => 
      -- Check if it's an arrow type by seeing if it's a forall with non-dependent body
      match e with
      | Expr.forallE _ _ body _ => !body.hasLooseBVar 0 && isImplOnly body
      | _ => true  -- Atomic proposition
    | Expr.const _ _ => true  -- Atomic proposition  
    | Expr.fvar _ => true    -- Variable/hypothesis
    | Expr.sort _ => true    -- Prop
    | _ => true              -- Other atomic cases

  let goal ← getMainGoal
  let goalType ← goal.getType
  
  if !isImplOnly goalType then
    throwError "Goal contains non-implication connectives"

  -- Repeatedly introduce implications until we reach an atomic goal
  partial def introduceAll (g : MVarId) : TacticM MVarId := do
    withMVarContext g do
      let gType ← g.getType
      if gType.isForall then
        let (newGoal, _) ← g.intro `h
        introduceAll newGoal
      else
        return g

  -- Try to prove goal using assumptions and forward chaining
  partial def proveAtomic (g : MVarId) (depth : Nat := 10) : TacticM Unit := do
    if depth = 0 then
      throwError "Search depth exceeded"
    
    withMVarContext g do
      let goalType ← g.getType
      let lctx ← getLCtx
      
      -- First try direct assumption match
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let declType ← inferType (Expr.fvar decl.fvarId)
        try
          if ← isDefEq goalType declType then
            g.assign (Expr.fvar decl.fvarId)
            return
        catch _ => continue
      
      -- Try forward chaining: look for implications A → B where we can prove A
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let declType ← inferType (Expr.fvar decl.fvarId)
        
        -- Check if this is an implication
        if declType.isForall && !declType.bindingBody!.hasLooseBVar 0 then
          let antecedent := declType.bindingDomain!
          let consequent := declType.bindingBody!
          
          -- Check if consequent matches our goal
          try
            if ← isDefEq goalType consequent then
              -- Try to prove the antecedent
              let antMVar ← mkFreshExprSyntheticOpaqueMVar antecedent
              
              -- Recursively try to prove antecedent
              try
                proveAtomic antMVar.mvarId! (depth - 1)
                -- If successful, apply modus ponens
                let proof ← mkAppM' (Expr.fvar decl.fvarId) #[antMVar]
                g.assign proof
                return
              catch _ => continue
          catch _ => continue
      
      throwError f!"Cannot prove goal: {goalType}"

  -- Main algorithm
  let atomicGoal ← introduceAll goal
  proveAtomic atomicGoal
  
  return ()

-- Test theorems for prove_impl_tautology

theorem test_1 (A : Prop) : A → A := by
  run_tac prove_impl_tautology

theorem test_2 (A B : Prop) : A → B → A := by
  run_tac prove_impl_tautology

theorem test_3 (P Q : Prop) : P → Q → Q := by
  run_tac prove_impl_tautology

theorem test_4 (A B C : Prop) : A → (B → C) → B → C := by
  run_tac prove_impl_tautology

theorem test_5 (X Y : Prop) : (X → Y) → X → Y := by
  run_tac prove_impl_tautology

theorem test_6 (P Q R : Prop) : (P → Q → R) → Q → P → R := by
  run_tac prove_impl_tautology

theorem test_7 (A B C : Prop) : (A → B) → (B → C) → A → C := by
  run_tac prove_impl_tautology

theorem test_8 (X Y : Prop) : (X → X → Y) → X → Y := by
  run_tac prove_impl_tautology

theorem test_9 (P Q R S : Prop) : P → Q → R → S → P := by
  run_tac prove_impl_tautology

theorem test_10 (A B C : Prop) : (A → B → C) → (A → B) → A → C := by
  run_tac prove_impl_tautology

theorem test_11 (X Y Z W : Prop) : (X → Y → Z) → (X → Y) → X → Z := by
  run_tac prove_impl_tautology

theorem test_12 (P Q R : Prop) : ((P → Q) → R) → (P → Q) → R := by
  run_tac prove_impl_tautology

theorem test_13 (A B C D : Prop) : (A → B → C → D) → A → B → C → D := by
  run_tac prove_impl_tautology

theorem test_14 (X Y Z : Prop) : (X → Y → Z) → (Y → X → Z) := by
  run_tac prove_impl_tautology

theorem test_15 (P Q R S : Prop) : ((P → Q) → R → S) → (P → Q) → R → S := by
  run_tac prove_impl_tautology