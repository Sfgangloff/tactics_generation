# Lean LSP MCP Tool Usage Log

This log tracks all lean-lsp-mcp tool invocations during the decide_list_theory tactic development.

---

## Milestone 1: Skeleton and principled failure

### Tool: lean_diagnostic_messages
- **File:** `decide_list_theory.milestone1.lean`
- **Purpose:** Verify milestone 1 compiles correctly
- **Result:** Initial errors:
  - `List.mem` unknown constant → Changed to use only `Membership.mem` and `Eq`
  - `List.get?` unknown constant → Removed from unsupported ops list
  - Type mismatch on return → Added `return` keyword
- **Final Result:** Success - compiles with expected `#check_failure` info messages

### Tool: lean_loogle
- **Query:** `List _ Membership`
- **Purpose:** Find correct membership constant name
- **Result:** No results - used `Membership.mem` instead

### Tool: lean_local_search
- **Query:** `List.Mem`
- **Purpose:** Verify List.Mem exists
- **Result:** Empty - confirmed need to use `Membership.mem`

---

## Milestone 2: Concrete list equality

### Tool: lean_loogle
- **Query:** `List.append List.cons`
- **Purpose:** Find append normalization lemmas
- **Result:** Found key lemmas:
  - `List.append.eq_1`: `[].append x = x`
  - `List.append.eq_2`: `(a :: as).append x = a :: as.append x`
  - `List.append_eq`: `as.append bs = as ++ bs`

### Tool: lean_diagnostic_messages
- **File:** `decide_list_theory.milestone2.lean`
- **Purpose:** Verify milestone 2 compiles
- **Result:** Success - all 10 tests pass, `#check_failure` tests confirm correct rejections

---

## Milestone 3: Length arithmetic

### Tool: lean_loogle
- **Query:** `List.length_append`
- **Purpose:** Find length lemmas for append
- **Result:** Found `List.length_append : (as ++ bs).length = as.length + bs.length`

### Tool: lean_loogle
- **Query:** `List.length_cons`
- **Purpose:** Find length lemma for cons
- **Result:** Found `List.length_cons : (a :: as).length = as.length + 1`

### Tool: lean_diagnostic_messages
- **File:** `decide_list_theory.milestone3.lean`
- **Purpose:** Verify milestone 3 compiles
- **Result:** Initial errors - detection logic too strict for length goals
- **Fix:** Changed `isListProposition` to use `||` instead of requiring both conditions

### Tool: lean_goal
- **File:** `decide_list_theory.milestone3.lean` (lines 214, 220)
- **Purpose:** Debug failing length tests
- **Result:** Goals `l.length + 0 = l.length` and `0 ≤ l.length` needed omega directly

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone3.lean`
- **Result:** Success - all 12 tests pass after improving `tryLengthArithmetic` to try omega first

---

## Milestone 4: Membership basics

### Tool: lean_loogle
- **Query:** `List.mem_cons`
- **Purpose:** Find membership lemma for cons
- **Result:** Found `List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`

### Tool: lean_loogle
- **Query:** `List.not_mem_nil`
- **Purpose:** Find non-membership lemma for empty list
- **Result:** Found `List.not_mem_nil : a ∉ []`

### Tool: lean_diagnostic_messages
- **File:** `decide_list_theory.milestone4.lean`
- **Purpose:** Verify milestone 4 compiles
- **Result:** Initial failure on `¬(a ∈ [])` - goal simplified to `¬False`

### Tool: lean_goal
- **File:** `decide_list_theory.milestone4.lean` (line 267)
- **Purpose:** Debug failing test
- **Result:** Goal `¬False` after simp - needed `not_false_eq_true` lemma

### Tool: lean_diagnostic_messages (final)
- **Result:** Success after adding `not_false_eq_true` to simp lemmas

---

## Milestone 5: Append membership

### Tool: lean_loogle
- **Query:** `List.mem_append`
- **Purpose:** Find append membership lemma
- **Result:** Found `List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`

### Tool: lean_diagnostic_messages
- **File:** `decide_list_theory.milestone5.lean`
- **Purpose:** Verify milestone 5 compiles
- **Result:** Success - all tests pass including append membership and iff test

---

## Milestone 6: List structural induction

### Tool: lean_diagnostic_messages (attempt 1)
- **File:** `decide_list_theory.milestone6.lean`
- **Purpose:** Verify initial M6 implementation compiles
- **Result:** Errors — `induction l with | nil => ... | cons => ...` syntax not allowed inside `evalTactic` quotes ("unexpected token 'with'")
- **Fix:** Replaced `with` syntax with `<;>` combinator: `induction l <;> simp_all [...]`

### Tool: lean_multi_attempt
- **File:** `decide_list_theory.milestone6.lean`, line 319
- **Purpose:** Find tactics that prove `∀ (l : List Nat), l ++ [] = l`
- **Result:** All four tactics close the goal (empty goals):
  - `intro l; simp [List.append_nil]` ✓
  - `intro l; induction l <;> simp_all [List.cons_append, List.append_nil]` ✓
  - `simp [List.append_nil]` ✓ (closes directly)
  - `intro l; induction l <;> simp [List.cons_append, List.append_nil]` ✓

### Tool: lean_diagnostic_messages (attempt 2)
- **File:** `decide_list_theory.milestone6.lean`
- **Purpose:** Verify after adding `tryForallSimp` with `simp only [...]`
- **Result:** Tests 1 and 2 still fail — `simp only [...]` in multiline tactic quote not closing goal
- **Fix:** Changed to single-line `;`-separated form and removed `only` keyword: `intro l; simp [List.append_nil, ...]`

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone6.lean`
- **Result:** Success — all tests pass. Key fix: use `simp` without `only` in single-line tactic quote

---

## Milestone 7: Logical connectives

### Tool: lean_diagnostic_messages (attempt 1)
- **File:** `decide_list_theory.milestone7.lean`
- **Purpose:** Verify initial M7 implementation compiles
- **Result:** Two errors: (1) invalid `@[...]` attribute syntax in `private def leafSimpLemmas` (removed); (2) `decide_list_theory: could not prove compound goal` on `3 ∈ [1, 2] ∨ 1 ∈ [1, 2]`
- **Fix:** Removed invalid helper def, rewrote compound handlers

### Tool: lean_diagnostic_messages (attempt 2)
- **File:** `decide_list_theory.milestone7.lean`
- **Purpose:** Verify after removing leafSimpLemmas and adding `<|>`
- **Result:** `<|>` not valid in tactic quotes ("unexpected token '<|>'")
- **Fix:** Changed to `first | ... | ...` form

### Tool: lean_diagnostic_messages (attempt 3)
- **File:** `decide_list_theory.milestone7.lean`
- **Purpose:** Verify after switching to `first | ...`
- **Result:** `3 ∈ [1, 2] ∨ 1 ∈ [1, 2]` still fails — root cause: `simp` doesn't throw when it can't close a goal, so `first | (left; simp)` silently leaves goals open. Replaced with tactics that always throw: `decide`, `omega`, `aesop`. Also `isCompoundGoal` intercepts before `isMembershipGoal`, so needed `decide` as first attempt.
- **Fix:** Try `decide` first in `tryDisjunction`/`tryConjunction`; use flat `first | (left; decide) | (right; decide) | ...` to avoid nesting issues

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone7.lean`
- **Result:** Success — all tests pass including conjunction, disjunction, and implication goals

---

## Milestone 8: Normalization pass

### Tool: lean_diagnostic_messages (attempt 1)
- **File:** `decide_list_theory.milestone8.lean`
- **Purpose:** Verify M8 implementation compiles
- **Result:** Success with one warning: `unused variable 'normalized'`
- **Fix:** Changed `let normalized ← tryNormalize` to `let _ ← tryNormalize`

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone8.lean`
- **Result:** Success — all tests pass. Normalization via `simp only [List.append_nil, List.nil_append, List.length_nil, List.append_assoc, ...]` fires before dispatch, canonicalizing goals before rule matching.

---

## Milestone 9: Guardrails and complexity bounds

### Tool: lean_loogle
- **Query:** `Expr.depth`
- **Purpose:** Find built-in expression depth function
- **Result:** No results — wrote custom `partial def exprDepth` and `exprSize`

### Tool: lean_local_search
- **Query:** `Expr.numSubexprs`
- **Purpose:** Find built-in expression size function
- **Result:** No results — confirmed need for custom helpers

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone9.lean`
- **Result:** Success on first attempt. All previous tests pass. Three new `#check_failure` tests confirm:
  - Nested list quantifiers (`∀ l₁ l₂ : List Nat, ...`) rejected with "depth 2" message
  - Unsupported op (reverse) rejected
  - Non-list goal rejected

---

## Milestone 10: Internal refactor for long-term stability

### Tool: lean_diagnostic_messages (attempt 1)
- **File:** `decide_list_theory.milestone10.lean`
- **Purpose:** Verify M10 refactored architecture compiles
- **Result:** Two errors:
  1. `Unknown identifier 'v'` at line 117 — typo in `containsUnsupportedOps`: `.forallE` branch had `visit t; visit v; visit b` but `v` is only in `.letE`. Fixed to `visit t; visit b`.
  2. `Unknown identifier 'Lake.Ref'` — used `Lake.Ref`/`Lake.mkRef` for trace flag, which is the build system API not core Lean. Replaced with `initialize Lean.registerTraceClass \`decide_list_theory` and `trace[decide_list_theory] "..."` macro.

### Tool: lean_diagnostic_messages (final)
- **File:** `decide_list_theory.milestone10.lean`
- **Result:** Success — all tests pass. Clean architecture with:
  - `GoalType` inductive (listEquality | lengthArithmetic | membership | forallList | compound | implication | unsupported)
  - `classify : Expr → MetaM GoalType`
  - `normalize : TacticM Bool`
  - `applyRule : GoalType → TacticM Unit`
  - `trace[decide_list_theory]` tracing via `registerTraceClass`

---
