/-
  decide_list_theory — Milestone 2: Concrete list equality

  Builds on Milestone 1 to add:
  - Proving equalities between concrete lists using `rfl`
  - Normalizing append expressions with simp lemmas
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
      -- Check for unsupported operations
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
  if !hasList then return false
  let hasSupported ← containsSupportedListOps e
  return hasSupported

/-- Check if the goal is a list equality -/
def isListEquality (e : Expr) : MetaM Bool := do
  match e.eq? with
  | some (ty, _, _) =>
    -- Check if the type is a List
    match ty with
    | .app (.const ``List _) _ => return true
    | _ => return false
  | none => return false

/-- Try to prove list equality using rfl after normalization -/
def tryListEqualityRfl : TacticM Bool := do
  try
    -- First try rfl directly
    evalTactic (← `(tactic| rfl))
    return true
  catch _ =>
    return false

/-- Try to prove list equality by normalizing with simp then rfl -/
def tryListEqualitySimp : TacticM Bool := do
  try
    -- Normalize append expressions, then try rfl
    evalTactic (← `(tactic| simp only [List.append_eq, List.append_nil, List.nil_append]))
    -- Check if goal is closed
    let goals ← getGoals
    return goals.isEmpty
  catch _ =>
    return false

/-- Main tactic implementation -/
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

  -- Try list equality rules (Milestone 2)
  let isEq ← isListEquality goal
  if isEq then
    -- Try rfl first
    if ← tryListEqualityRfl then return
    -- Try simp normalization
    if ← tryListEqualitySimp then return
    throwError "decide_list_theory: could not prove list equality"

  -- No matching rule found
  throwError "decide_list_theory: no applicable rule found for this goal"

/-- The decide_list_theory tactic for automatically proving list-related goals -/
elab "decide_list_theory" : tactic => decideListTheoryImpl

end DecideListTheory

-- ============================================================
-- Tests for Milestone 2
-- ============================================================

section Tests

-- Test 1: Simple concrete list equality (rfl)
example : [1, 2, 3] = [1, 2, 3] := by decide_list_theory

-- Test 2: Empty list equality
example : ([] : List Nat) = [] := by decide_list_theory

-- Test 3: Single element list
example : [42] = [42] := by decide_list_theory

-- Test 4: Append with nil on right
example : [1, 2] ++ [] = [1, 2] := by decide_list_theory

-- Test 5: Append with nil on left
example : [] ++ [1, 2] = [1, 2] := by decide_list_theory

-- Test 6: Simple append
example : [1] ++ [2] = [1, 2] := by decide_list_theory

-- Test 7: Multiple append
example : [1] ++ [2] ++ [3] = [1, 2, 3] := by decide_list_theory

-- Test 8: Nested append
example : ([1] ++ [2]) ++ [3] = [1, 2, 3] := by decide_list_theory

-- Test 9: Variables in concrete positions (should work with rfl)
example (a b : Nat) : [a, b] = [a, b] := by decide_list_theory

-- Test 10: Append with variables
example (a b : Nat) : [a] ++ [b] = [a, b] := by decide_list_theory

-- Test 11: Should still reject unsupported operations
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])

-- Test 12: Should still reject non-list goals
#check_failure (by decide_list_theory : 1 + 1 = 2)

end Tests
