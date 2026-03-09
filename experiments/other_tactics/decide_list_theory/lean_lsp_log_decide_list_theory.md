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

(Not yet started)

---

## Milestone 7: Logical connectives

(Not yet started)

---

## Milestone 8: Normalization pass

(Not yet started)

---

## Milestone 9: Guardrails and complexity bounds

(Not yet started)

---

## Milestone 10: Internal refactor for long-term stability

(Not yet started)

---
