/-
  decide_list_theory — Milestone 7: Logical connectives

  Builds on Milestone 6 to add:
  - Compound goals: P ∧ Q, P ∨ Q  (explicit decomposition)
  - Implication goals: P → Q       (intro + leaf dispatch)
  These complement the existing decide/simp/aesop paths with
  a predictable, structure-directed strategy.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

open Lean Elab Tactic Meta

namespace DecideListTheory

/-- Check if an expression mentions List type -/
def mentionsList (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const ``List _ => found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

/-- Check if an expression contains list operations we support -/
def containsSupportedListOps (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ =>
      if n == ``List.length || n == ``List.append || n == ``List.cons ||
         n == ``List.nil || n == ``Membership.mem || n == ``Eq then
        found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

/-- Check if an expression contains unsupported list operations -/
def containsUnsupportedListOps (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ =>
      if n == ``List.reverse || n == ``List.filter || n == ``List.map ||
         n == ``List.foldl || n == ``List.foldr || n == ``List.take ||
         n == ``List.drop || n == ``List.head? || n == ``List.tail? ||
         n == ``List.zip then
        found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

/-- Classify whether the goal is a supported list proposition -/
def isListProposition (e : Expr) : MetaM Bool := do
  let hasList ← mentionsList e
  let hasSupported ← containsSupportedListOps e
  return hasList || hasSupported

/-- Check if the goal is a list equality -/
def isListEquality (e : Expr) : MetaM Bool := do
  match e.eq? with
  | some (ty, _, _) =>
    match ty with
    | .app (.const ``List _) _ => return true
    | _ => return false
  | none => return false

/-- Check if the goal involves List.length -/
def involvesLength (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ =>
      if n == ``List.length then found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

/-- Check if the goal is a membership proposition (a ∈ l or a ∉ l) -/
def isMembershipGoal (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ =>
      if n == ``Membership.mem then found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

/-- Check if the outermost ∀ binds a List-typed variable (Milestone 6) -/
def isForallListGoal (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ ty _ _ =>
    match ty with
    | .app (.const ``List _) _ => return true
    | _ => return false
  | _ => return false

/-- Check if goal is a top-level conjunction (∧) or disjunction (∨) (Milestone 7) -/
def isCompoundGoal (e : Expr) : MetaM Bool := do
  match e with
  | .app (.app (.const ``And _) _) _ => return true
  | .app (.app (.const ``Or  _) _) _ => return true
  | _ => return false

/-- Check if goal is an implication (∀ _ : P, Q) where P is not a List type (Milestone 7) -/
def isImplicationGoal (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ ty _ _ =>
    match ty with
    | .app (.const ``List _) _ => return false  -- handled by isForallListGoal
    | _ => return true
  | _ => return false

/-- Try to prove list equality using rfl after normalization -/
def tryListEqualityRfl : TacticM Bool := do
  try
    evalTactic (← `(tactic| rfl))
    return true
  catch _ =>
    return false

/-- Try to prove list equality by normalizing with simp then rfl -/
def tryListEqualitySimp : TacticM Bool := do
  try
    evalTactic (← `(tactic| simp only [List.append_eq, List.append_nil, List.nil_append]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ =>
    return false

/-- Try to prove length goal by normalizing and using omega -/
def tryLengthArithmetic : TacticM Bool := do
  try
    evalTactic (← `(tactic| omega))
    return true
  catch _ =>
    try
      evalTactic (← `(tactic|
        simp only [List.length_cons, List.length_nil, List.length_append,
                   List.length_singleton, List.append_nil, List.nil_append,
                   add_zero, zero_add] <;> omega))
      return true
    catch _ =>
      try
        evalTactic (← `(tactic|
          simp only [List.length_cons, List.length_nil, List.length_append,
                     List.length_singleton, List.append_nil, List.nil_append,
                     add_zero, zero_add]))
        let goals ← getGoals
        return goals.isEmpty
      catch _ =>
        return false

/-- Try to prove membership goal using decide (for concrete lists) -/
def tryMembershipDecide : TacticM Bool := do
  try
    evalTactic (← `(tactic| decide))
    return true
  catch _ =>
    return false

/-- Try to prove membership goal using simp with membership lemmas (including append) -/
def tryMembershipSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append,
                 or_false, false_or, true_or, or_true,
                 not_false_eq_true, not_true_eq_false]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ =>
    return false

/-- Try to prove membership using aesop for more complex goals -/
def tryMembershipAesop : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append] <;> aesop))
    return true
  catch _ =>
    return false

/-- Try to prove ∀ l, P l using intro + omega -/
def tryForallOmega : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; omega))
    return true
  catch _ => return false

/-- Try to prove ∀ l, P l by intro + simp -/
def tryForallSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; simp [List.append_nil, List.nil_append,
      List.length_nil, List.length_cons, List.length_append]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Try to prove ∀ l, P l by intro + structural induction + simp_all -/
def tryForallInduction : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; induction l <;>
      simp_all [List.cons_append, List.append_nil, List.nil_append,
        List.length_cons, List.length_nil]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Try to prove ∀ l, P l by intro + induction + simp + omega -/
def tryForallInductionOmega : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; induction l <;>
      (simp [List.length_cons, List.length_nil, List.append_nil,
             List.nil_append, List.cons_append] <;> omega)))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Try to prove a conjunction (P ∧ Q) (Milestone 7).
    Tries `decide` first (handles all concrete decidable cases), then splits and
    applies leaf tactics. Only uses tactics that throw on failure. -/
def tryConjunction : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => pure ()
  try
    evalTactic (← `(tactic| constructor <;> (first | decide | omega | aesop)))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Try to prove a disjunction (P ∨ Q) (Milestone 7).
    Tries `decide` first (handles all concrete decidable cases), then tries structural
    decomposition.  Uses a flat `first` sequence to avoid nested `|` parsing issues. -/
def tryDisjunction : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => pure ()
  try
    evalTactic (← `(tactic|
      first | (left; decide) | (right; decide)
            | (left; omega)  | (right; omega)
            | (left; aesop)  | (right; aesop)))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Try to prove an implication (P → Q) by introducing P and applying leaf tactics (Milestone 7) -/
def tryImplication : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => pure ()
  try
    evalTactic (← `(tactic| intro _h; first | decide | omega | assumption | aesop))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

/-- Main tactic implementation (Milestone 7) -/
def decideListTheoryImpl : TacticM Unit := do
  let goal ← getMainTarget

  -- Check for unsupported operations first
  let hasUnsupported ← containsUnsupportedListOps goal
  if hasUnsupported then
    throwError "decide_list_theory: unsupported list operation detected (e.g., reverse, filter, map)"

  -- Check if this is a list proposition we can handle
  let isListProp ← isListProposition goal
  if !isListProp then
    throwError "decide_list_theory: goal is not a supported list proposition"

  -- Rule 0: Universally quantified list goals (Milestone 6)
  let isForall ← isForallListGoal goal
  if isForall then
    if ← tryForallOmega then return
    if ← tryForallSimp then return
    if ← tryForallInduction then return
    if ← tryForallInductionOmega then return
    throwError "decide_list_theory: could not prove universally quantified list goal"

  -- Rule 0.5: Compound logical goals (Milestone 7)
  let isCompound ← isCompoundGoal goal
  if isCompound then
    if ← tryConjunction then return
    if ← tryDisjunction then return
    throwError "decide_list_theory: could not prove compound (∧/∨) list goal"

  -- Rule 0.6: Implication goals (Milestone 7)
  let isImpl ← isImplicationGoal goal
  if isImpl then
    if ← tryImplication then return
    throwError "decide_list_theory: could not prove implication list goal"

  -- Rule 1: List equality (Milestone 2)
  let isEq ← isListEquality goal
  if isEq then
    if ← tryListEqualityRfl then return
    if ← tryListEqualitySimp then return
    throwError "decide_list_theory: could not prove list equality"

  -- Rule 2: Membership (Milestones 4-5)
  let isMem ← isMembershipGoal goal
  if isMem then
    if ← tryMembershipDecide then return
    if ← tryMembershipSimp then return
    if ← tryMembershipAesop then return
    throwError "decide_list_theory: could not prove membership goal"

  -- Rule 3: Length arithmetic (Milestone 3)
  let hasLength ← involvesLength goal
  if hasLength then
    if ← tryLengthArithmetic then return
    throwError "decide_list_theory: could not prove length goal"

  -- No matching rule found
  throwError "decide_list_theory: no applicable rule found for this goal"

/-- The decide_list_theory tactic for automatically proving list-related goals -/
elab "decide_list_theory" : tactic => decideListTheoryImpl

end DecideListTheory

-- ============================================================
-- Tests for Milestone 7
-- ============================================================

section Tests

-- Previous tests still work (Milestones 2-6)
example : [1, 2, 3] = [1, 2, 3] := by decide_list_theory
example : [1] ++ [2] = [1, 2] := by decide_list_theory
example : [1, 2, 3].length = 3 := by decide_list_theory
example : 1 ∈ [1, 2, 3] := by decide_list_theory
example : 1 ∉ ([] : List Nat) := by decide_list_theory
example : 1 ∈ [1, 2] ++ [3, 4] := by decide_list_theory
example : 5 ∉ [1, 2] ++ [3, 4] := by decide_list_theory
example (a : Nat) : a ∈ [a] ++ [1, 2] := by decide_list_theory
example (a : Nat) : a ∈ [1, 2] ++ [a] := by decide_list_theory
example (a : Nat) (l₁ l₂ : List Nat) : a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by decide_list_theory
example : ∀ (l : List Nat), l ++ [] = l := by decide_list_theory
example : ∀ (l : List Nat), [] ++ l = l := by decide_list_theory
example : ∀ (l : List Nat), l.length ≥ 0 := by decide_list_theory

-- New tests for logical connectives (Milestone 7)

-- Test 1: Conjunction of concrete membership facts
example : 1 ∈ [1, 2] ∧ 2 ∈ [1, 2] := by decide_list_theory

-- Test 2: Conjunction mixing length and membership
example : [1, 2].length = 2 ∧ 1 ∈ [1, 2] := by decide_list_theory

-- Test 3: Disjunction where left holds
example : 1 ∈ [1, 2] ∨ 3 ∈ [1, 2] := by decide_list_theory

-- Test 4: Disjunction where right holds
example : 3 ∈ [1, 2] ∨ 1 ∈ [1, 2] := by decide_list_theory

-- Test 5: Conjunction with free variable (decide won't work, needs simp)
example (a : Nat) : a ∈ [a] ++ [1] ∧ a ∈ [1] ++ [a] := by decide_list_theory

-- Test 6: Implication — hypothesis not needed, conclusion proved directly
example : (1 : Nat) ∈ [1, 2] → [1, 2].length = 2 := by decide_list_theory

-- Test 7: Implication — trivial via omega on concrete length
example : (1 : Nat) ∈ [1, 2] → [1, 2].length > 0 := by decide_list_theory

-- Test 8: Conjunction of two equalities
example : ([1, 2] ++ []).length = 2 ∧ ([] ++ [1, 2]).length = 2 := by decide_list_theory

-- Rejection tests still work
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])
#check_failure (by decide_list_theory : 1 + 1 = 2)

end Tests
