decide_list_theory — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `decide_list_theory` that evolves through milestones. Each milestone strictly refines the previous one: it either proves more goals, improves robustness, or increases safety — never weakening earlier behavior.

We enforce:
1. Monotonic test suite (never delete tests unless intentionally changing behavior).
2. Deterministic rule ordering.
3. Conservative normalization.
4. Delegation to existing tactics (simp, omega, decide) when appropriate.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behavior:
- If the goal is not a supported list proposition, fail with a clear message.
- Detect goals involving `List`, `length`, `(++)`, `(∈)`, `(=)`.
- If unsupported operations appear, fail with "unsupported list operation".

Architecture (future-proof):
- normalize goal
- classify goal type
- try rules in fixed order
- fail with informative message

This dispatcher remains unchanged throughout the project.

--------------------------------------------------

Milestone 2 — Concrete list equality
------------------------------------
New capability:
Prove equalities between concrete lists:

    [1, 2, 3] = [1, 2, 3]
    [a] ++ [b] = [a, b]

Implementation:
- Use `rfl` for definitionally equal lists
- Use `simp only [List.cons_append, List.nil_append]` for append normalization

Important constraints:
- Only handle fully concrete lists initially
- No variables in lists yet

--------------------------------------------------

Milestone 3 — Length arithmetic
-------------------------------
New capability:
Prove goals involving `length`:

    length [1, 2, 3] = 3
    length (l₁ ++ l₂) = length l₁ + length l₂
    length l = 0 → l = []

Implementation:
1. Normalize with `simp only [List.length_cons, List.length_nil, List.length_append]`
2. Delegate arithmetic to `omega`

Key lemmas:
- `List.length_nil`: `length [] = 0`
- `List.length_cons`: `length (a :: l) = length l + 1`
- `List.length_append`: `length (l₁ ++ l₂) = length l₁ + length l₂`

--------------------------------------------------

Milestone 4 — Membership basics
-------------------------------
New capability:
Prove membership goals:

    a ∈ [a, b, c]
    a ∈ (a :: l)
    a ∉ []

Implementation:
- Use `List.mem_cons_iff`: `a ∈ (b :: l) ↔ a = b ∨ a ∈ l`
- Use `List.not_mem_nil`: `¬(a ∈ [])`
- For concrete lists, use `decide` when element type has `DecidableEq`

Important:
- Require `DecidableEq α` for the element type
- Handle both `∈` and `∉` notation

--------------------------------------------------

Milestone 5 — Append membership
-------------------------------
New capability:
Handle membership with concatenation:

    a ∈ l₁ → a ∈ (l₁ ++ l₂)
    a ∈ l₂ → a ∈ (l₁ ++ l₂)
    a ∈ (l₁ ++ l₂) ↔ a ∈ l₁ ∨ a ∈ l₂

Key lemma:
- `List.mem_append`: `a ∈ (l₁ ++ l₂) ↔ a ∈ l₁ ∨ a ∈ l₂`

Implementation:
- Normalize append expressions
- Apply `List.mem_append` to decompose
- Recurse on subgoals

--------------------------------------------------

Milestone 6 — List structural induction
---------------------------------------
New capability:
Handle goals with list variables via case analysis:

    ∀ l, l ++ [] = l
    ∀ l, length l ≥ 0

Implementation:
- Detect when goal has free list variables
- Apply `List.cases_on` or `List.rec` for case splitting
- Handle `[]` and `(a :: l)` cases separately

Important:
- Limit recursion depth to prevent infinite loops
- Use `induction` tactic as fallback

--------------------------------------------------

Milestone 7 — Logical connectives
---------------------------------
New capability:
Handle compound goals with ∧, ∨, →, ¬:

    a ∈ l ∧ b ∈ l → length l ≥ 2
    a ∈ l ∨ a ∈ m → a ∈ (l ++ m)

Implementation:
- Decompose conjunctions with `And.intro`
- Handle disjunctions with `Or.inl`, `Or.inr`, or case split
- Process implications by introducing hypotheses
- Handle negations appropriately

This milestone combines all previous rules with propositional logic.

--------------------------------------------------

Milestone 8 — Normalization pass
--------------------------------
Before dispatching rules, run a lightweight normalization step.

Goals:
- Canonicalize list expressions
- Simplify redundant operations
- Improve pattern matching

Good rewrites:
- `l ++ []` → `l`
- `[] ++ l` → `l`
- `length []` → `0`
- Nested appends: `(l₁ ++ l₂) ++ l₃` → `l₁ ++ (l₂ ++ l₃)` (right-associative)

Avoid:
- Expanding definitions unnecessarily
- Unbounded simplification

--------------------------------------------------

Milestone 9 — Guardrails and complexity bounds
----------------------------------------------
Add safety checks:

1. **Unsupported operations**: Reject goals with `List.reverse`, `List.filter`, `List.map`, etc.
2. **Quantifier check**: Reject goals with nested quantifiers over lists
3. **Complexity bounds**:
   - Term depth > 10 → fail
   - Term size > 100 → fail
4. **Decidability check**: Ensure `DecidableEq` is available when needed

Goal: Increase trust in the tactic by failing fast on unsupported cases.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
-------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
normalize    : Expr → TacticM Expr
classify     : Expr → Option GoalType
applyRule    : GoalType → TacticM Unit
```

where `GoalType` is:
```lean
inductive GoalType where
  | listEquality
  | lengthArithmetic
  | membership
  | compound
  | unsupported
```

Also add trace option `trace.decide_list_theory` printing:
- detected goal type
- applied rule
- lemmas used

--------------------------------------------------

Ordering Discipline
-------------------
Rule priority (from most specific to most general):

1. Concrete equality (`rfl`)
2. Membership in concrete list (`decide`)
3. Length arithmetic (`omega`)
4. Append properties (`simp` + specific lemmas)
5. Structural induction (case analysis)
6. Compound logic (decomposition)
7. Failure with informative message

--------------------------------------------------

Guiding Principle for Future Growth
----------------------------------
When encountering a new list property you want automated:

DO NOT immediately make the tactic smarter.

Instead:
1. Prove a clean standalone lemma.
2. Add a rule that applies exactly that lemma.

This keeps `decide_list_theory` predictable and maintainable.

--------------------------------------------------

Summary of Milestones
--------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Principled failure |
| 2 | Concrete equality | `[1,2] = [1,2]` |
| 3 | Length arithmetic | `length` + `omega` |
| 4 | Membership basics | `a ∈ [a,b,c]` |
| 5 | Append membership | `a ∈ (l₁ ++ l₂)` |
| 6 | Structural induction | Case analysis on list variables |
| 7 | Logical connectives | ∧, ∨, →, ¬ |
| 8 | Normalization | Canonicalization pass |
| 9 | Guardrails | Safety checks |
| 10 | Refactor | Clean architecture + tracing |
