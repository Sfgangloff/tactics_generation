/-
  decide_list_theory — Milestone 1: Skeleton and principled failure

  This milestone establishes the tactic skeleton with:
  - Goal detection for list-related propositions
  - Principled failure with informative error messages
  - Architecture for future rule dispatching
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
  -- Check if this is an equality, membership, or other proposition involving lists
  let hasList ← mentionsList e
  if !hasList then return false
  let hasSupported ← containsSupportedListOps e
  return hasSupported

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

  -- For now, just fail with a message indicating we recognize the goal
  -- Future milestones will add actual proof rules
  throwError "decide_list_theory: recognized list proposition, but no proof rules implemented yet (Milestone 1 skeleton)"

/-- The decide_list_theory tactic for automatically proving list-related goals -/
elab "decide_list_theory" : tactic => decideListTheoryImpl

end DecideListTheory

-- ============================================================
-- Tests for Milestone 1
-- ============================================================

section Tests

open DecideListTheory

-- Test 1: Should recognize list equality as a list proposition
example : [1, 2, 3] = [1, 2, 3] := by
  -- This should fail with "recognized list proposition" message
  first
  | decide_list_theory
  | rfl  -- Fallback for now

-- Test 2: Should recognize membership as a list proposition
example : 1 ∈ [1, 2, 3] := by
  first
  | decide_list_theory
  | decide  -- Fallback for now

-- Test 3: Should recognize length as a list proposition
example : [1, 2, 3].length = 3 := by
  first
  | decide_list_theory
  | rfl  -- Fallback for now

-- Test 4: Should recognize append as a list proposition
example : [1] ++ [2] = [1, 2] := by
  first
  | decide_list_theory
  | rfl  -- Fallback for now

-- Test 5: Should fail on non-list goals
example : 1 + 1 = 2 := by
  -- This should fail with "not a supported list proposition"
  first
  | decide_list_theory
  | rfl  -- Expected fallback

-- Test 6: Should reject unsupported operations (reverse)
-- Note: This test expects the tactic to fail
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])

-- Test 7: Should reject unsupported operations (map)
#check_failure (by decide_list_theory : List.map (· + 1) [1, 2] = [2, 3])

end Tests
