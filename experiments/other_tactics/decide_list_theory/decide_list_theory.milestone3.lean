/-
  decide_list_theory — Milestone 3: Length arithmetic

  Builds on Milestone 2 to add:
  - Proving goals involving `length`
  - Normalizing length expressions with simp lemmas
  - Delegating arithmetic to `omega`
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
  -- A list proposition is one that either:
  -- 1. Mentions List type (for list equalities, membership)
  -- 2. Contains supported list operations (for length goals on numeric types)
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
    -- Try omega directly first (handles many cases like 0 ≤ l.length)
    evalTactic (← `(tactic| omega))
    return true
  catch _ =>
    try
      -- Normalize length expressions then try omega
      evalTactic (← `(tactic|
        simp only [List.length_cons, List.length_nil, List.length_append,
                   List.length_singleton, List.append_nil, List.nil_append,
                   add_zero, zero_add] <;> omega))
      return true
    catch _ =>
      try
        -- Fallback: just simp and check if solved
        evalTactic (← `(tactic|
          simp only [List.length_cons, List.length_nil, List.length_append,
                     List.length_singleton, List.append_nil, List.nil_append,
                     add_zero, zero_add]))
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

  -- Rule 1: List equality (Milestone 2)
  let isEq ← isListEquality goal
  if isEq then
    if ← tryListEqualityRfl then return
    if ← tryListEqualitySimp then return
    throwError "decide_list_theory: could not prove list equality"

  -- Rule 2: Length arithmetic (Milestone 3)
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
-- Tests for Milestone 3
-- ============================================================

section Tests

-- Previous tests still work (Milestone 2)
example : [1, 2, 3] = [1, 2, 3] := by decide_list_theory
example : [1] ++ [2] = [1, 2] := by decide_list_theory

-- New tests for length (Milestone 3)

-- Test 1: Length of empty list
example : ([] : List Nat).length = 0 := by decide_list_theory

-- Test 2: Length of concrete list
example : [1, 2, 3].length = 3 := by decide_list_theory

-- Test 3: Length of singleton
example : [42].length = 1 := by decide_list_theory

-- Test 4: Length after append
example : ([1, 2] ++ [3, 4]).length = 4 := by decide_list_theory

-- Test 5: Length equation with variables
example (l₁ l₂ : List Nat) : (l₁ ++ l₂).length = l₁.length + l₂.length := by decide_list_theory

-- Test 6: Length inequality
example : [1, 2].length ≤ 5 := by decide_list_theory

-- Test 7: Length comparison
example : [1].length < [1, 2, 3].length := by decide_list_theory

-- Test 8: Complex length arithmetic
example (l : List Nat) : l.length + 0 = l.length := by decide_list_theory

-- Test 9: Length with nested appends
example : (([1] ++ [2]) ++ [3]).length = 3 := by decide_list_theory

-- Test 10: Length non-negativity (omega handles this)
example (l : List Nat) : 0 ≤ l.length := by decide_list_theory

-- Rejection tests still work
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])
#check_failure (by decide_list_theory : 1 + 1 = 2)

end Tests
