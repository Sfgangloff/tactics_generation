generated_tactic (ac_rw) — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `ac_rw` that rewrites goals modulo associativity and
commutativity of declared AC-operators. Each milestone strictly refines the previous
one: it either handles more operators, deeper expressions, or more lemma forms, never
weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic candidate enumeration order.
3. Conservative AC-unification: prefer the first matching candidate.
4. Delegation to standard `rw` whenever AC-normalization is unnecessary.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Tactic syntax: `ac_rw [h]` where `h` is a single rewrite lemma.
- If the goal contains no AC-operator subexpressions, fail with a clear message.
- Detect whether a binary operator has both `IsAssociative` and `IsCommutative` instances.
- If no AC-operator is found, fail with "ac_rw: no AC-operator in goal".

Architecture:
- parse lemma list
- detect AC-operators in goal
- enumerate candidates
- attempt AC-unification
- perform rewrite
- fail informatively

--------------------------------------------------

Milestone 2 — Flat AC-rewriting for addition (ℕ)
--------------------------------------------------
New capability:
Rewrite in goals where all top-level subexpressions use `+` on `ℕ` or `ℤ`:

    example (a b c : ℕ) : a + b + c = c + a + b := by ac_rw [add_comm]
    example (a b c : ℕ) : a + (0 + b) + c = a + b + c := by ac_rw [zero_add]

Implementation:
- Flatten the goal's AC-subexpression into a list of arguments.
- For each permutation, attempt standard `rw`.
- Left-associate to create canonical form, then permute with `add_left_comm`.

Important constraints:
- Only handle a single AC-operator (`+`) initially.
- Only flat (depth-1) expressions.

--------------------------------------------------

Milestone 3 — Multiplication AC-rewriting
------------------------------------------
New capability:
Extend to the `*` operator on commutative (semi)rings:

    example (a b c : ℕ) : a * b * c = c * a * b := by ac_rw [mul_comm]
    example (a b : ℕ) : a * 1 * b = a * b := by ac_rw [mul_one]

Implementation:
- Generalise the Milestone 2 engine to work on any operator with
  `IsAssociative` and `IsCommutative` instances.
- Use `mul_left_comm` for permutation.

--------------------------------------------------

Milestone 4 — Nested AC-expressions
-------------------------------------
New capability:
Handle expressions where AC-subterms appear nested under other operations:

    example (a b c d : ℕ) : a + (b + c) + d = a + (c + b) + d := by ac_rw [add_comm]
    example (a b c : ℕ) : (a + b) * c = (b + a) * c := by ac_rw [add_comm]

Implementation:
- Recursively traverse the goal expression.
- At each AC-subterm, attempt the AC-rewrite.
- Apply only to the first matching subterm (deterministic).

--------------------------------------------------

Milestone 5 — Lemmas with premises
------------------------------------
New capability:
Support rewrite lemmas that have dischargeable side-conditions:

    example (a b c : ℕ) (h : a = 0) : a + b + c = b + c := by ac_rw [add_zero]

Implementation:
- After AC-unification succeeds, attempt to discharge each premise using
  `assumption` or `norm_num`.
- If a premise cannot be discharged automatically, try to leave it as a
  new subgoal (configurable).

--------------------------------------------------

Milestone 6 — Multiple lemmas
------------------------------
New capability:
Apply a list of rewrite lemmas in sequence:

    example (a b c : ℕ) : a + (b + c) * 1 = a + b + c := by ac_rw [mul_one, add_assoc]

Implementation:
- Process each lemma in the list left-to-right.
- After each successful rewrite, update the goal and continue.
- Stop when no further rewrite applies.

--------------------------------------------------

Milestone 7 — Right-hand side rewriting
-----------------------------------------
New capability:
Rewrite right-to-left using `← lemma`:

    example (a b c : ℕ) : a + b + c = (a + c) + b := by ac_rw [← add_comm]

Implementation:
- Detect `← lemma` syntax.
- Swap LHS and RHS of the lemma before AC-unification.

--------------------------------------------------

Milestone 8 — Set and lattice operators
-----------------------------------------
New capability:
Support additional AC-operators beyond `+` and `*`:

    example (A B C : Set α) : A ∪ B ∪ C = C ∪ A ∪ B := by ac_rw [Set.union_comm]
    example (a b c : Bool) : (a || b) && c = c && (b || a) := by ac_rw [Bool.and_comm, Bool.or_comm]

Implementation:
- Generalise the AC-operator detection to any binary operation with the
  required type class instances.
- No special-casing — rely on the generic engine.

--------------------------------------------------

Milestone 9 — Guardrails and complexity bounds
----------------------------------------------
Add safety checks:

1. **Depth limit**: Stop AC-flattening at depth > 8 to prevent exponential blowup.
2. **Permutation limit**: Abort if the number of AC-permutations exceeds 5040 (7!).
3. **Missing instances**: Fail clearly when `IsAssociative`/`IsCommutative` not found.
4. **Cycle detection**: Prevent rewrites that reproduce the original goal.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
detectACOps   : Expr → TacticM (List Expr)
flattenAC     : Expr → Name → List Expr
acUnify       : List Expr → List Expr → TacticM Subst
reshapeToMatch : Expr → Expr → Name → TacticM Expr
```

Also add trace option `trace.ac_rw` printing:
- AC-operators detected
- flattened argument list
- candidate subterms tried
- reshaping steps applied

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Principled failure |
| 2 | Flat `+` rewriting | ℕ/ℤ addition AC-rewrite |
| 3 | `*` operator | Commutative (semi)rings |
| 4 | Nested expressions | AC-subterms under other ops |
| 5 | Lemmas with premises | Dischargeable side-conditions |
| 6 | Multiple lemmas | Sequence of rewrites |
| 7 | `←` rewriting | Right-to-left lemma |
| 8 | Other AC-ops | Sets, lattices, etc. |
| 9 | Guardrails | Depth/permutation limits |
| 10 | Refactor | Clean architecture + tracing |
