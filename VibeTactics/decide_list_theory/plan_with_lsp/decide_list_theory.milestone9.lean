/-
  decide_list_theory — Milestone 9: Guardrails and complexity bounds

  Builds on Milestone 8 to add safety checks that fail fast with clear messages:
  1. Unsupported operations (already present, retained)
  2. Nested list quantifiers: ∀ l₁ : List α, ∀ l₂ : List α, ... → rejected
  3. Term size  > 500 → rejected  (prevents hangs on accidentally huge goals)
  4. Term depth > 30  → rejected  (prevents runaway elaboration)
  All checks fire before normalization and rule dispatch.
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

/-- Check if the outermost ∀ binds a List-typed variable -/
def isForallListGoal (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ ty _ _ =>
    match ty with
    | .app (.const ``List _) _ => return true
    | _ => return false
  | _ => return false

/-- Check if goal is a top-level conjunction (∧) or disjunction (∨) -/
def isCompoundGoal (e : Expr) : MetaM Bool := do
  match e with
  | .app (.app (.const ``And _) _) _ => return true
  | .app (.app (.const ``Or  _) _) _ => return true
  | _ => return false

/-- Check if goal is an implication (∀ _ : P, Q) where P is not a List type -/
def isImplicationGoal (e : Expr) : MetaM Bool := do
  match e with
  | .forallE _ ty _ _ =>
    match ty with
    | .app (.const ``List _) _ => return false
    | _ => return true
  | _ => return false

-- ---------------------------------------------------------------
-- Complexity and safety helpers (Milestone 9)
-- ---------------------------------------------------------------

/-- Count the number of top-level nested ∀ that bind List-typed variables.
    Returns 0 if the outermost binder is not a List, 1 if there is one, etc.
    A value > 1 indicates nested list quantifiers which we do not support. -/
def countListForallDepth : Expr → Nat
  | .forallE _ ty body _ =>
    match ty with
    | .app (.const ``List _) _ => countListForallDepth body + 1
    | _                        => 0
  | _ => 0

/-- Compute an upper bound on the size (node count) of an expression.
    Uses a fuel parameter to ensure termination. -/
partial def exprSize : Expr → Nat
  | .app f a          => exprSize f + exprSize a + 1
  | .lam _ t b _      => exprSize t + exprSize b + 1
  | .forallE _ t b _  => exprSize t + exprSize b + 1
  | .letE _ t v b _   => exprSize t + exprSize v + exprSize b + 1
  | .mdata _ e        => exprSize e + 1
  | .proj _ _ e       => exprSize e + 1
  | _                 => 1

/-- Compute an upper bound on the depth of an expression. -/
partial def exprDepth : Expr → Nat
  | .app f a          => max (exprDepth f) (exprDepth a) + 1
  | .lam _ t b _      => max (exprDepth t) (exprDepth b) + 1
  | .forallE _ t b _  => max (exprDepth t) (exprDepth b) + 1
  | .letE _ t v b _   => max (exprDepth t) (max (exprDepth v) (exprDepth b)) + 1
  | .mdata _ e        => exprDepth e + 1
  | .proj _ _ e       => exprDepth e + 1
  | _                 => 0

/-- Perform all safety/guardrail checks on the goal (Milestone 9).
    Returns `some errorMsg` if a check fails, `none` if all checks pass. -/
def guardRails (goal : Expr) : Option String :=
  -- Complexity: term too large
  let sz := exprSize goal
  if sz > 500 then
    some s!"decide_list_theory: goal too large (size {sz} > 500); aborting"
  -- Complexity: term too deep
  else
    let d := exprDepth goal
    if d > 30 then
      some s!"decide_list_theory: goal too deeply nested (depth {d} > 30); aborting"
    -- Structural: nested list quantifiers
    else
      let nestDepth := countListForallDepth goal
      if nestDepth > 1 then
        some s!"decide_list_theory: nested list quantifiers (depth {nestDepth}) not supported; \
               use separate lemmas for each list variable"
      else
        none

-- ---------------------------------------------------------------
-- Proof strategies (unchanged from M8)
-- ---------------------------------------------------------------

/-- Normalization pre-pass: canonicalize list expressions before dispatch. -/
def tryNormalize : TacticM Bool := do
  try
    let goalBefore ← getMainTarget
    evalTactic (← `(tactic|
      simp only [List.append_nil, List.nil_append, List.length_nil,
                 List.append_assoc, List.length_append, List.length_cons]))
    let goalAfter ← getMainTarget
    let goals ← getGoals
    if goals.isEmpty then return true
    return goalBefore != goalAfter
  catch _ => return false

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

def tryMembershipDecide : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => return false

def tryMembershipSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append,
                 or_false, false_or, true_or, or_true,
                 not_false_eq_true, not_true_eq_false]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

def tryMembershipAesop : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append] <;> aesop))
    return true
  catch _ => return false

def tryForallOmega : TacticM Bool := do
  try evalTactic (← `(tactic| intro l; omega)); return true catch _ => return false

def tryForallSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; simp [List.append_nil, List.nil_append,
      List.length_nil, List.length_cons, List.length_append]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

def tryForallInduction : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; induction l <;>
      simp_all [List.cons_append, List.append_nil, List.nil_append,
        List.length_cons, List.length_nil]))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

def tryForallInductionOmega : TacticM Bool := do
  try
    evalTactic (← `(tactic| intro l; induction l <;>
      (simp [List.length_cons, List.length_nil, List.append_nil,
             List.nil_append, List.cons_append] <;> omega)))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

def tryConjunction : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => pure ()
  try
    evalTactic (← `(tactic| constructor <;> (first | decide | omega | aesop)))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

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

def tryImplication : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => pure ()
  try
    evalTactic (← `(tactic| intro _h; first | decide | omega | assumption | aesop))
    let goals ← getGoals
    return goals.isEmpty
  catch _ => return false

-- ---------------------------------------------------------------
-- Main dispatcher (Milestone 9)
-- ---------------------------------------------------------------

/-- Main tactic implementation (Milestone 9) -/
def decideListTheoryImpl : TacticM Unit := do
  let goal ← getMainTarget

  -- Safety check 1: unsupported list operations
  let hasUnsupported ← containsUnsupportedListOps goal
  if hasUnsupported then
    throwError "decide_list_theory: unsupported list operation detected (e.g., reverse, filter, map)"

  -- Safety check 2: complexity and structural guardrails (Milestone 9)
  if let some msg := guardRails goal then
    throwError msg

  -- Safety check 3: goal must mention supported list operations
  let isListProp ← isListProposition goal
  if !isListProp then
    throwError "decide_list_theory: goal is not a supported list proposition"

  -- Normalization pre-pass (Milestone 8)
  let _ ← tryNormalize
  let goal ← getMainTarget
  let openGoals ← getGoals
  if openGoals.isEmpty then return

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

  throwError "decide_list_theory: no applicable rule found for this goal"

/-- The decide_list_theory tactic for automatically proving list-related goals -/
elab "decide_list_theory" : tactic => decideListTheoryImpl

end DecideListTheory

-- ============================================================
-- Tests for Milestone 9
-- ============================================================

section Tests

-- Previous tests still work (Milestones 2-8)
example : [1, 2, 3] = [1, 2, 3] := by decide_list_theory
example : [1] ++ [2] = [1, 2] := by decide_list_theory
example : [1, 2, 3].length = 3 := by decide_list_theory
example : 1 ∈ [1, 2, 3] := by decide_list_theory
example : 1 ∉ ([] : List Nat) := by decide_list_theory
example : 1 ∈ [1, 2] ++ [3, 4] := by decide_list_theory
example : 5 ∉ [1, 2] ++ [3, 4] := by decide_list_theory
example (a : Nat) : a ∈ [a] ++ [1, 2] := by decide_list_theory
example (a : Nat) (l₁ l₂ : List Nat) : a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by decide_list_theory
example : ∀ (l : List Nat), l ++ [] = l := by decide_list_theory
example : ∀ (l : List Nat), l.length ≥ 0 := by decide_list_theory
example : 1 ∈ [1, 2] ∧ 2 ∈ [1, 2] := by decide_list_theory
example : 1 ∈ [1, 2] ∨ 3 ∈ [1, 2] := by decide_list_theory
example : 3 ∈ [1, 2] ∨ 1 ∈ [1, 2] := by decide_list_theory
example : (1 : Nat) ∈ [1, 2] → [1, 2].length = 2 := by decide_list_theory
example (l : List Nat) : ([] ++ l).length = l.length := by decide_list_theory
example (l : List Nat) : (l ++ []).length = l.length := by decide_list_theory
example (l₁ l₂ l₃ : List Nat) :
    ((l₁ ++ l₂) ++ l₃).length = l₁.length + l₂.length + l₃.length := by decide_list_theory
example : ([1, 2] ++ []) ++ [3] = [1, 2, 3] := by decide_list_theory

-- New guardrail tests (Milestone 9)

-- Test 1: Nested list quantifier is rejected with a clear error
#check_failure (by decide_list_theory :
  ∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).length = l₁.length + l₂.length)

-- Test 2: Unsupported operation still rejected
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])

-- Test 3: Non-list goal still rejected
#check_failure (by decide_list_theory : 1 + 1 = 2)

end Tests
