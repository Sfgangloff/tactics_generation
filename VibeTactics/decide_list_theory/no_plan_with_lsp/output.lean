import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# decide_list_theory

A tactic for deciding statements in the first-order theory of lists.
Handles goals involving length, concatenation, membership, and structural
properties by combining simp normalization, omega for arithmetic, and
tauto/aesop for propositional reasoning.

## Algorithm

1. Try `decide` for closed ground goals (concrete lists).
2. Normalize with a curated `simp only` set of list lemmas, then close
   with `rfl | omega | tauto | aesop`.
3. Introduce all universal quantifiers via `intros`, then repeat step 2.
4. Fall back to `aesop` for goals with richer logical structure.
-/

/-- `decide_list_theory` proves quantifier-free statements in the first-order
theory of lists. Handled fragments:
- List equality / inequality (structural decomposition via `simp`)
- Length relationships (delegated to `omega`)
- Membership predicates (`∈`, `∉`, with `simp` + `tauto`)
- Concatenation identities and associativity
- Propositional combinations (`∧`, `∨`, `→`, `↔`) via `tauto`/`aesop`

For concrete (ground) goals it falls back to `decide`. -/
macro "decide_list_theory" : tactic =>
  `(tactic|
    first
    -- Branch 1: closed/ground goals decidable by kernel reduction
    | decide
    -- Branch 2: pure simp normalization, then close residual goal
    | (simp only [List.length_nil, List.length_cons, List.length_append,
                  List.length_singleton,
                  List.append_nil, List.nil_append, List.append_assoc,
                  List.cons_append, List.singleton_append,
                  List.mem_cons, List.mem_nil_iff, List.mem_append,
                  List.mem_singleton, List.not_mem_nil,
                  List.cons_ne_nil, List.cons_eq_cons,
                  Nat.add_zero, Nat.zero_add, Nat.succ_eq_add_one,
                  or_false, false_or, and_true, true_and, or_true, true_or,
                  eq_self_iff_true, ne_eq]
       <;> first | rfl | omega | tauto | aesop)
    -- Branch 3: introduce all universally-quantified variables first, then normalize
    | (intros
       <;> simp only [List.length_nil, List.length_cons, List.length_append,
                      List.length_singleton,
                      List.append_nil, List.nil_append, List.append_assoc,
                      List.cons_append, List.singleton_append,
                      List.mem_cons, List.mem_nil_iff, List.mem_append,
                      List.mem_singleton, List.not_mem_nil,
                      List.cons_ne_nil, List.cons_eq_cons,
                      Nat.add_zero, Nat.zero_add, Nat.succ_eq_add_one,
                      or_false, false_or, and_true, true_and, or_true, true_or,
                      eq_self_iff_true, ne_eq]
       <;> first | rfl | omega | tauto | aesop)
    -- Branch 4: broad fallback
    | aesop)

-- ============================================================
-- Test Suite
-- ============================================================

section Tests

-- ------------------------------------------------------------
-- 1. Basic structural properties
-- ------------------------------------------------------------

-- List appended with empty is itself
theorem test_1 : ∀ (l : List ℕ), l ++ [] = l := by decide_list_theory

-- Length of cons
theorem test_2 : ∀ (a : ℕ) (l : List ℕ), (a :: l).length = l.length + 1 := by
  decide_list_theory

-- Length of append
theorem test_3 : ∀ (l₁ l₂ : List ℕ), (l₁ ++ l₂).length = l₁.length + l₂.length := by
  decide_list_theory

-- Append associativity
theorem test_4 : ∀ (l₁ l₂ l₃ : List ℕ), l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ := by
  decide_list_theory

-- Empty list prepended
theorem test_5 : ∀ (l : List ℕ), [] ++ l = l := by decide_list_theory

-- ------------------------------------------------------------
-- 2. Membership predicates
-- ------------------------------------------------------------

-- Not a member of empty list
theorem test_6 : ∀ (a : ℕ), ¬(a ∈ ([] : List ℕ)) := by decide_list_theory

-- Membership decomposition for cons
theorem test_7 : ∀ (a b : ℕ) (l : List ℕ), a ∈ (b :: l) → a = b ∨ a ∈ l := by
  decide_list_theory

-- Head is always a member
theorem test_8 : ∀ (a : ℕ) (l : List ℕ), a ∈ (a :: l) := by decide_list_theory

-- Membership in append (left side)
theorem test_9 : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ l₁ → a ∈ (l₁ ++ l₂) := by
  decide_list_theory

-- Membership in append (right side)
theorem test_10 : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ l₂ → a ∈ (l₁ ++ l₂) := by
  decide_list_theory

-- Membership in append iff
theorem test_11 : ∀ (a : ℕ) (l₁ l₂ : List ℕ), a ∈ (l₁ ++ l₂) ↔ a ∈ l₁ ∨ a ∈ l₂ := by
  decide_list_theory

-- ------------------------------------------------------------
-- 3. Length arithmetic
-- ------------------------------------------------------------

-- Length of empty list
theorem test_12 : ([] : List ℕ).length = 0 := by decide_list_theory

-- Length of singleton
theorem test_13 : ∀ (a : ℕ), [a].length = 1 := by decide_list_theory

-- Length inequality: non-empty list has positive length
theorem test_14 : ∀ (a : ℕ) (l : List ℕ), (a :: l).length > 0 := by decide_list_theory

-- Combined length: fixed sizes
theorem test_15 : ∀ (l₁ l₂ : List ℕ),
    l₁.length = 2 → l₂.length = 3 → (l₁ ++ l₂).length = 5 := by decide_list_theory

-- Length of double cons
theorem test_16 : ∀ (a b : ℕ) (l : List ℕ), (a :: b :: l).length = l.length + 2 := by
  decide_list_theory

-- ------------------------------------------------------------
-- 4. Concrete list examples
-- ------------------------------------------------------------

-- Concrete append
theorem test_17 : ([1, 2] ++ [3] : List ℕ) = [1, 2, 3] := by decide_list_theory

-- Concrete membership and length
theorem test_18 : (2 : ℕ) ∈ [1, 2, 3] ∧ [1, 2, 3].length = 3 := by decide_list_theory

-- Concrete non-membership
theorem test_19 : (4 : ℕ) ∉ [1, 2, 3] := by decide_list_theory

-- Concrete equality
theorem test_20 : ([1, 2, 3] : List ℕ) = [1, 2, 3] := by decide_list_theory

-- ------------------------------------------------------------
-- 5. Compound / logical combinations
-- ------------------------------------------------------------

-- Membership in l implies membership in l ++ l (hypothesis is used by tauto)
theorem test_21 : ∀ (a : ℕ) (l : List ℕ), a ∈ l → a ∈ (l ++ l) := by decide_list_theory

-- From two memberships, membership in cons follows
theorem test_22 : ∀ (a b : ℕ) (l : List ℕ),
    (a ∈ l ∧ b ∈ l) → (a ∈ (b :: l) ∨ l.length > 0) := by decide_list_theory

-- Membership in cons iff
theorem test_23 : ∀ (a b : ℕ) (l : List ℕ),
    a ∈ (b :: l) ↔ a = b ∨ a ∈ l := by decide_list_theory

-- Length monotone under append
theorem test_24 : ∀ (l₁ l₂ : List ℕ), l₁.length ≤ (l₁ ++ l₂).length := by
  decide_list_theory

-- Append length symmetry
theorem test_25 : ∀ (l₁ l₂ : List ℕ),
    (l₁ ++ l₂).length = (l₂ ++ l₁).length := by decide_list_theory

end Tests
