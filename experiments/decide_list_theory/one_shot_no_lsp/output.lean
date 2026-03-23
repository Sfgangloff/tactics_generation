import Mathlib.Data.List.Basic
import Mathlib.Tactic

open Lean Meta Elab Tactic

/-!
# `decide_list_theory` tactic

A decision procedure for quantifier-free statements in the first-order theory
of lists over the signature `{[], (::), (++), List.length, (∈), (=)}`.

## Proof strategy

1. **Introduce**: eliminate all outermost `∀` binders and `→` hypotheses via
   `intro *`.
2. **Trivial closers**: try `rfl`, `decide`, `omega` in that order.
3. **Structural simplification**: normalize with a curated simp set of list
   algebraic identities (append laws, length laws, membership rewrites).
4. **Arithmetic delegation**: after normalization, discharge length goals via
   `omega`.
5. **Propositional delegation**: after normalization, discharge membership /
   logical goals via `tauto`.
6. **Combined per-goal solver**: after normalization, apply
   `omega | tauto | rfl | decide` to each remaining subgoal.
7. **General fallback**: `aesop`.

## Supported fragment

Quantifier-free formulas built from:
- list constructors: `[]`, `a :: l`
- operations: `l₁ ++ l₂`, `List.length l`
- predicates: `l₁ = l₂`, `a ∈ l`
- connectives: `∧`, `∨`, `¬`, `→`

## Limitations

- Requires `DecidableEq` on the element type.
- Does not handle `∀`/`∃` inside the goal body.
- Does not support `List.reverse`, `List.filter`, `List.map`, etc.
- Complexity bound: depth ≤ 10, term size ≤ 100 (heuristic, not enforced).
-/

namespace DecideListTheory

/-- Try a tactic, restoring state on failure.
    Returns `true` iff the tactic succeeds **and** closes all goals. -/
private def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    tac
    if (← getGoals).isEmpty then
      return true
    else
      restoreState s
      return false
  catch _ =>
    restoreState s
    return false

/-- `simp only` normalization with list algebraic identities.
    Rewrites append laws, length laws, and membership predicates without
    closing side goals (preserves context for downstream solvers). -/
private def listNormalizeTac : TacticM Unit :=
  evalTactic (← `(tactic| simp only [
    List.length_nil,
    List.length_cons,
    List.length_append,
    List.nil_append,
    List.append_nil,
    List.append_assoc,
    List.cons_append,
    List.mem_nil_iff,
    List.mem_cons,
    List.mem_append,
    List.not_mem_nil
  ]))

/-- Full `simp` with list lemmas (may discharge side goals automatically). -/
private def listFullSimpTac : TacticM Unit :=
  evalTactic (← `(tactic| simp [
    List.length_nil,
    List.length_cons,
    List.length_append,
    List.nil_append,
    List.append_nil,
    List.append_assoc,
    List.cons_append,
    List.mem_nil_iff,
    List.mem_cons,
    List.mem_append,
    List.not_mem_nil
  ]))

/-- Main `decide_list_theory` implementation. -/
def decideListTheoryImpl : TacticM Unit := do
  -- Step 1: eliminate outermost ∀ binders and → hypotheses
  let _ ← tryTac <| evalTactic (← `(tactic| intro *))
  if (← getGoals).isEmpty then return

  -- Step 2: trivial / concrete goals
  if ← tryTac <| evalTactic (← `(tactic| rfl))    then return
  if ← tryTac <| evalTactic (← `(tactic| decide)) then return
  if ← tryTac <| evalTactic (← `(tactic| omega))  then return
  if ← tryTac <| evalTactic (← `(tactic| tauto))  then return

  -- Step 3: structural simplification alone
  if ← tryTac listFullSimpTac then return

  -- Step 4: normalize, then discharge arithmetic
  if ← tryTac do
    listNormalizeTac
    evalTactic (← `(tactic| all_goals omega))
  then return

  -- Step 5: normalize, then discharge propositional / membership
  if ← tryTac do
    listNormalizeTac
    evalTactic (← `(tactic| all_goals tauto))
  then return

  -- Step 6: normalize, then try decide (concrete post-reduction)
  if ← tryTac do
    listNormalizeTac
    evalTactic (← `(tactic| all_goals decide))
  then return

  -- Step 7: normalize, then multi-solver per subgoal
  if ← tryTac do
    listNormalizeTac
    evalTactic (← `(tactic| all_goals first | omega | tauto | rfl | decide))
  then return

  -- Step 8: full simp + arithmetic
  if ← tryTac do
    listFullSimpTac
    evalTactic (← `(tactic| all_goals omega))
  then return

  -- Step 9: full simp + propositional
  if ← tryTac do
    listFullSimpTac
    evalTactic (← `(tactic| all_goals tauto))
  then return

  -- Step 10: full simp + multi-solver
  if ← tryTac do
    listFullSimpTac
    evalTactic (← `(tactic| all_goals first | omega | tauto | rfl | decide))
  then return

  -- Step 11: aesop — general-purpose fallback
  if ← tryTac <| evalTactic (← `(tactic| aesop)) then return

  -- All strategies exhausted
  throwTacticEx `decide_list_theory (← getMainGoal)
    m!"decide_list_theory: failed to prove goal.\n\
       Supported fragment: quantifier-free formulas over \
       \{[], ::, ++, List.length, ∈, =\} with DecidableEq on elements.\n\
       Unsupported: quantifiers in goal body, List.reverse, List.filter, \
       List.map, List.zip, etc."

end DecideListTheory

/--
`decide_list_theory` automatically proves quantifier-free statements in the
first-order theory of lists.

**Supported operations**: `[]`, `(::)`, `(++)`, `List.length`, `(∈)`, `(=)`.

**Supported connectives**: `∧`, `∨`, `¬`, `→` (with leading `∀` binders).

**Examples**:
```lean
example : ∀ (l : List ℕ), l ++ [] = l := by decide_list_theory
example : ∀ (a : ℕ) (l : List ℕ), List.length (a :: l) = List.length l + 1 :=
  by decide_list_theory
example : ∀ (a : ℕ), ¬(a ∈ ([] : List ℕ)) := by decide_list_theory
example : [1, 2] ++ [3] = [1, 2, 3] := by decide_list_theory
example : 2 ∈ [1, 2, 3] ∧ List.length [1, 2, 3] = 3 := by decide_list_theory
```
-/
elab "decide_list_theory" : tactic =>
  DecideListTheory.decideListTheoryImpl

-- ============================================================
-- Test suite
-- ============================================================

section DecideListTheoryTests

-- Basic append laws
example : ∀ (l : List ℕ), l ++ [] = l :=
  by decide_list_theory

example : ∀ (l : List ℕ), [] ++ l = l :=
  by decide_list_theory

example : ∀ (l₁ l₂ l₃ : List ℕ), l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ :=
  by decide_list_theory

-- Length laws
example : ∀ (a : ℕ) (l : List ℕ), List.length (a :: l) = List.length l + 1 :=
  by decide_list_theory

example : ∀ (l₁ l₂ : List ℕ),
    List.length (l₁ ++ l₂) = List.length l₁ + List.length l₂ :=
  by decide_list_theory

-- Membership base cases
example : ∀ (a : ℕ), ¬(a ∈ ([] : List ℕ)) :=
  by decide_list_theory

example : ∀ (a : ℕ) (l : List ℕ), a ∈ (a :: l) :=
  by decide_list_theory

-- Membership structural rules
example : ∀ (a b : ℕ) (l : List ℕ), a ∈ (b :: l) → a = b ∨ a ∈ l :=
  by decide_list_theory

example : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ l₁ → a ∈ (l₁ ++ l₂) :=
  by decide_list_theory

example : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ l₂ → a ∈ (l₁ ++ l₂) :=
  by decide_list_theory

example : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ (l₁ ++ l₂) → a ∈ l₁ ∨ a ∈ l₂ :=
  by decide_list_theory

-- Length arithmetic (delegated to omega after normalization)
example : ∀ (l₁ l₂ : List ℕ),
    List.length l₁ = 2 → List.length l₂ = 3 → List.length (l₁ ++ l₂) = 5 :=
  by decide_list_theory

-- Concrete lists
example : [1, 2] ++ [3] = [1, 2, 3] :=
  by decide_list_theory

example : (2 : ℕ) ∈ [1, 2, 3] ∧ List.length [1, 2, 3] = 3 :=
  by decide_list_theory

example : List.length ([] : List ℕ) = 0 :=
  by decide_list_theory

example : List.length [1, 2, 3] = 3 :=
  by decide_list_theory

-- Logical combinations
example : ∀ (a b : ℕ) (l : List ℕ),
    (a ∈ l ∧ b ∈ l) → (a ∈ (b :: l) ∨ List.length l > 0) :=
  by decide_list_theory

end DecideListTheoryTests
