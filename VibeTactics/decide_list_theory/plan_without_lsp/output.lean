/-
  decide_list_theory — Single-file incremental implementation (plan, no LSP)

  Milestones implemented:
    1  Skeleton and principled failure
    2  Concrete list equality
    3  Length arithmetic
    4  Membership basics
    5  Append membership
    6  Structural induction
    7  Logical connectives
    8  Normalization pass
    9  Guardrails and complexity bounds
   10  Internal refactor (GoalType + trace)

  All milestone test suites are accumulated below.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

open Lean Elab Tactic Meta

namespace DecideListTheory

-- ================================================================
-- Milestone 9 helpers: complexity bounds
-- ================================================================

partial def exprSize : Expr → Nat
  | .app f a         => exprSize f + exprSize a + 1
  | .lam _ t b _     => exprSize t + exprSize b + 1
  | .forallE _ t b _ => exprSize t + exprSize b + 1
  | .letE _ t v b _  => exprSize t + exprSize v + exprSize b + 1
  | .mdata _ e       => exprSize e + 1
  | .proj _ _ e      => exprSize e + 1
  | _                => 1

partial def exprDepth : Expr → Nat
  | .app f a         => max (exprDepth f) (exprDepth a) + 1
  | .lam _ t b _     => max (exprDepth t) (exprDepth b) + 1
  | .forallE _ t b _ => max (exprDepth t) (exprDepth b) + 1
  | .letE _ t v b _  => max (exprDepth t) (max (exprDepth v) (exprDepth b)) + 1
  | .mdata _ e       => exprDepth e + 1
  | .proj _ _ e      => exprDepth e + 1
  | _                => 0

def countListForallDepth : Expr → Nat
  | .forallE _ ty body _ =>
    match ty with
    | .app (.const ``List _) _ => countListForallDepth body + 1
    | _                        => 0
  | _ => 0

-- ================================================================
-- Milestone 10: GoalType inductive
-- ================================================================

/-- Classification of supported goal shapes. -/
inductive GoalType where
  | listEquality
  | lengthArithmetic
  | membership
  | forallList
  | compound
  | implication
  | unsupported
  deriving Repr

-- ================================================================
-- Internal detection helpers (Milestone 1 analysis + refinements)
-- ================================================================

private def mentionsList (e : Expr) : MetaM Bool := do
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

private def containsSupportedOps (e : Expr) : MetaM Bool := do
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

private def containsUnsupportedOps (e : Expr) : MetaM Bool := do
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

private def hasMembership (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ => if n == ``Membership.mem then found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

private def hasLength (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  let rec visit (e : Expr) : MetaM Unit := do
    if ← found.get then return
    match e with
    | .const n _ => if n == ``List.length then found.set true
    | .app f a => visit f; visit a
    | .lam _ t b _ => visit t; visit b
    | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ e => visit e
    | .proj _ _ e => visit e
    | _ => return
  visit e
  found.get

-- ================================================================
-- Milestone 10: classify
-- ================================================================

/-- Classify the shape of a goal expression into a GoalType. -/
def classify (e : Expr) : MetaM GoalType := do
  -- Guardrail: unsupported operations
  if ← containsUnsupportedOps e then
    return .unsupported

  -- Guardrail: complexity bounds (M9)
  if exprSize e > 500 then return .unsupported
  if exprDepth e > 30 then return .unsupported

  -- Universally quantified list
  match e with
  | .forallE _ ty _ _ =>
    match ty with
    | .app (.const ``List _) _ =>
      if countListForallDepth e > 1 then return .unsupported
      return .forallList
    | _ => return .implication
  | _ => pure ()

  -- Compound logic
  match e with
  | .app (.app (.const ``And _) _) _ => return .compound
  | .app (.app (.const ``Or  _) _) _ => return .compound
  | _ => pure ()

  -- Must mention lists
  let hasList ← mentionsList e
  let hasOps  ← containsSupportedOps e
  if !hasList && !hasOps then return .unsupported

  -- Content classification
  match e.eq? with
  | some (ty, _, _) =>
    match ty with
    | .app (.const ``List _) _ => return .listEquality
    | _ => pure ()
  | none => pure ()

  if ← hasMembership e then return .membership
  if ← hasLength e     then return .lengthArithmetic

  return .unsupported

-- ================================================================
-- Milestone 8/10: normalize
-- ================================================================

/-- Normalization pass: canonicalize list expressions before dispatch. -/
def normalize : TacticM Bool := do
  try
    let before ← getMainTarget
    evalTactic (← `(tactic|
      simp only [List.append_nil, List.nil_append, List.length_nil,
                 List.append_assoc, List.length_append, List.length_cons]))
    let after ← getMainTarget
    let goals ← getGoals
    if goals.isEmpty then return true
    return before != after
  catch _ => return false

-- ================================================================
-- Leaf proof strategies
-- ================================================================

private def tryRfl : TacticM Bool := do
  try evalTactic (← `(tactic| rfl)); return true catch _ => return false

private def trySimp : TacticM Bool := do
  try
    evalTactic (← `(tactic| simp only [List.append_eq, List.append_nil, List.nil_append]))
    return (← getGoals).isEmpty
  catch _ => return false

private def tryOmega : TacticM Bool := do
  try evalTactic (← `(tactic| omega)); return true catch _ => return false

private def tryOmegaWithSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.length_cons, List.length_nil, List.length_append,
                 List.length_singleton, List.append_nil, List.nil_append,
                 add_zero, zero_add] <;> omega))
    return true
  catch _ => return false

private def tryDecide : TacticM Bool := do
  try evalTactic (← `(tactic| decide)); return true catch _ => return false

private def tryMembershipSimp : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append,
                 or_false, false_or, true_or, or_true,
                 not_false_eq_true, not_true_eq_false]))
    return (← getGoals).isEmpty
  catch _ => return false

private def tryMembershipAesop : TacticM Bool := do
  try
    evalTactic (← `(tactic|
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                 List.mem_nil_iff, List.mem_append] <;> aesop))
    return true
  catch _ => return false

-- ================================================================
-- Milestone 10: applyRule dispatch
-- ================================================================

/-- Dispatch a proof attempt based on the classified goal type. -/
def applyRule (gt : GoalType) : TacticM Unit := do
  match gt with
  | .listEquality =>
    if ← tryRfl  then return
    if ← trySimp then return
    throwError "decide_list_theory [listEquality]: could not prove list equality"

  | .lengthArithmetic =>
    if ← tryOmega         then return
    if ← tryOmegaWithSimp then return
    throwError "decide_list_theory [lengthArithmetic]: could not prove length goal"

  | .membership =>
    if ← tryDecide         then return
    if ← tryMembershipSimp then return
    if ← tryMembershipAesop then return
    throwError "decide_list_theory [membership]: could not prove membership goal"

  | .forallList =>
    let strategies : List (TacticM Bool) := [
      do try evalTactic (← `(tactic| intro l; omega)); return true catch _ => return false,
      do try
           evalTactic (← `(tactic| intro l; simp [List.append_nil, List.nil_append,
             List.length_nil, List.length_cons, List.length_append]))
           return (← getGoals).isEmpty
         catch _ => return false,
      do try
           evalTactic (← `(tactic| intro l; induction l <;>
             simp_all [List.cons_append, List.append_nil, List.nil_append,
               List.length_cons, List.length_nil]))
           return (← getGoals).isEmpty
         catch _ => return false,
      do try
           evalTactic (← `(tactic| intro l; induction l <;>
             (simp [List.length_cons, List.length_nil, List.append_nil,
                    List.nil_append, List.cons_append] <;> omega)))
           return (← getGoals).isEmpty
         catch _ => return false
    ]
    for s in strategies do
      if ← s then return
    throwError "decide_list_theory [forallList]: could not prove universally quantified list goal"

  | .compound =>
    if ← tryDecide then return
    try
      evalTactic (← `(tactic| constructor <;> (first | decide | omega | aesop)))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    try
      evalTactic (← `(tactic|
        first | (left; decide) | (right; decide)
              | (left; omega)  | (right; omega)
              | (left; aesop)  | (right; aesop)))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    throwError "decide_list_theory [compound]: could not prove compound (∧/∨) list goal"

  | .implication =>
    if ← tryDecide then return
    try
      evalTactic (← `(tactic| intro _h; first | decide | omega | assumption | aesop))
      if (← getGoals).isEmpty then return
    catch _ => pure ()
    throwError "decide_list_theory [implication]: could not prove implication list goal"

  | .unsupported =>
    throwError "decide_list_theory: goal is unsupported (unsupported ops, too complex, or not a list proposition)"

-- ================================================================
-- Trace option (Milestone 10)
-- ================================================================

initialize Lean.registerTraceClass `decide_list_theory

-- ================================================================
-- Main tactic entry point
-- ================================================================

def decideListTheoryImpl : TacticM Unit := do
  let goal ← getMainTarget

  let gt ← classify goal
  trace[decide_list_theory] "goal: {goal}"
  trace[decide_list_theory] "classified as: {repr gt}"

  match gt with
  | .unsupported => applyRule .unsupported
  | _ =>
    let _ ← normalize
    let openGoals ← getGoals
    if openGoals.isEmpty then return
    let goal' ← getMainTarget
    let gt' ← classify goal'
    trace[decide_list_theory] "after normalization, classified as: {repr gt'}"
    applyRule gt'

/-- The decide_list_theory tactic for automatically proving list-related goals. -/
elab "decide_list_theory" : tactic => decideListTheoryImpl

end DecideListTheory

-- ================================================================
-- MILESTONE 1 TESTS — Skeleton and principled failure
-- ================================================================

section Milestone1

-- Unsupported: not a list proposition
#check_failure (by decide_list_theory : 1 + 1 = 2)
-- Unsupported: reverse is not in supported ops
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])

end Milestone1

-- ================================================================
-- MILESTONE 2 TESTS — Concrete list equality
-- ================================================================

section Milestone2

example : [1, 2, 3] = [1, 2, 3] := by decide_list_theory
example : [1] ++ [2] = [1, 2] := by decide_list_theory
example : [1, 2] ++ [3] = [1, 2, 3] := by decide_list_theory
example : ([] : List Nat) ++ [] = [] := by decide_list_theory

end Milestone2

-- ================================================================
-- MILESTONE 3 TESTS — Length arithmetic
-- ================================================================

section Milestone3

example : [1, 2, 3].length = 3 := by decide_list_theory
example : ([] : List Nat).length = 0 := by decide_list_theory
example (l : List Nat) : ([] ++ l).length = l.length := by decide_list_theory
example (l : List Nat) : (l ++ []).length = l.length := by decide_list_theory
example (l₁ l₂ l₃ : List Nat) :
    ((l₁ ++ l₂) ++ l₃).length = l₁.length + l₂.length + l₃.length := by decide_list_theory

end Milestone3

-- ================================================================
-- MILESTONE 4 TESTS — Membership basics
-- ================================================================

section Milestone4

example : 1 ∈ [1, 2, 3] := by decide_list_theory
example : 2 ∈ [1, 2, 3] := by decide_list_theory
example : 3 ∈ [1, 2, 3] := by decide_list_theory
example : 1 ∉ ([] : List Nat) := by decide_list_theory
example : 4 ∉ [1, 2, 3] := by decide_list_theory
example (a : Nat) : a ∈ [a] := by decide_list_theory

end Milestone4

-- ================================================================
-- MILESTONE 5 TESTS — Append membership
-- ================================================================

section Milestone5

example : 1 ∈ [1, 2] ++ [3, 4] := by decide_list_theory
example : 3 ∈ [1, 2] ++ [3, 4] := by decide_list_theory
example : 2 ∈ [1, 2] ++ [3, 4] := by decide_list_theory
example : 5 ∉ [1, 2] ++ [3, 4] := by decide_list_theory
example (a : Nat) : a ∈ [a] ++ [1, 2] := by decide_list_theory
example (a : Nat) : a ∈ [1, 2] ++ [a] := by decide_list_theory
example : 2 ∈ [1] ++ [2] ++ [3] := by decide_list_theory
example : 2 ∈ ([1] ++ [2]) ++ [3] := by decide_list_theory
example : 1 ∈ [] ++ [1] := by decide_list_theory
example : 1 ∈ [1] ++ [] := by decide_list_theory
example (a : Nat) (l₁ l₂ : List Nat) : a ∈ l₁ ++ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := by decide_list_theory

end Milestone5

-- ================================================================
-- MILESTONE 6 TESTS — Structural induction (∀ l : List α)
-- ================================================================

section Milestone6

example : ∀ (l : List Nat), l ++ [] = l := by decide_list_theory
example : ∀ (l : List Nat), l.length ≥ 0 := by decide_list_theory
example : ∀ (l : List Nat), ([] ++ l).length = l.length := by decide_list_theory

end Milestone6

-- ================================================================
-- MILESTONE 7 TESTS — Logical connectives
-- ================================================================

section Milestone7

example : 1 ∈ [1, 2] ∧ 2 ∈ [1, 2] := by decide_list_theory
example : 1 ∈ [1, 2] ∨ 3 ∈ [1, 2] := by decide_list_theory
example : 3 ∈ [1, 2] ∨ 1 ∈ [1, 2] := by decide_list_theory
example : (1 : Nat) ∈ [1, 2] → [1, 2].length = 2 := by decide_list_theory

end Milestone7

-- ================================================================
-- MILESTONE 8 TESTS — Normalization
-- ================================================================

section Milestone8

example : ([1, 2] ++ []) ++ [3] = [1, 2, 3] := by decide_list_theory
example (l : List Nat) : (l ++ []).length = l.length := by decide_list_theory

end Milestone8

-- ================================================================
-- MILESTONE 9 TESTS — Guardrails
-- ================================================================

section Milestone9

-- Unsupported: reverse
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])
-- Unsupported: not a list prop
#check_failure (by decide_list_theory : 1 + 1 = 2)
-- Guardrail: nested ∀ over lists (more than 1 level)
#check_failure (by decide_list_theory :
  ∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).length = l₁.length + l₂.length)

end Milestone9

-- ================================================================
-- MILESTONE 10 TESTS — Refactored architecture (regression)
-- ================================================================

section Milestone10

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
#check_failure (by decide_list_theory :
  ∀ (l₁ l₂ : List Nat), (l₁ ++ l₂).length = l₁.length + l₂.length)
#check_failure (by decide_list_theory : List.reverse [1, 2] = [2, 1])
#check_failure (by decide_list_theory : 1 + 1 = 2)

end Milestone10
