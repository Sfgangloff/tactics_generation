presburger — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `presburger` that decides goals in quantifier-free
Presburger arithmetic (linear integer/natural-number arithmetic) and extends to
limited existential quantification. Each milestone strictly refines the previous one:
it handles a larger fragment of linear arithmetic, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering.
3. Conservative normalization: reduce to `omega`-compatible forms when possible.
4. Delegation to existing tactics (`omega`, `linarith`, `norm_num`) as backends.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals involving linear arithmetic (`+`, `-`, `*` by constants, `≤`, `<`, `=`).
- If non-linear terms are detected (e.g., `x * y`), fail with a clear message.
- If quantifiers other than `∃` are present, fail with "presburger: universal
  quantifiers not supported".

Architecture (future-proof):
- check for non-linear terms
- normalize to standard form
- dispatch to solver
- fail informatively

--------------------------------------------------

Milestone 2 — Atomic linear constraints
-----------------------------------------
New capability:
Prove atomic linear inequalities and equalities over ℕ and ℤ:

    (x : ℤ) + 3 ≤ x + 5
    2 * (n : ℕ) + 3 ≤ 7 * n

Implementation:
- Dispatch directly to `omega` for goals in the `omega`-decidable fragment.
- This covers the vast majority of quantifier-free linear goals.

--------------------------------------------------

Milestone 3 — Logical connectives: conjunction and implication
--------------------------------------------------------------
New capability:
Handle conjunctive goals and implications:

    (x y : ℤ) → x + y ≤ 10 ∧ x - y ≥ 2 → 2 * x ≤ 12
    (a b : ℕ) → a + 2 * b = 8 → a ≤ 8

Implementation:
- Introduce hypotheses with `intro`.
- Decompose conjunctions with `constructor` / `And.intro`.
- Dispatch each sub-goal to `omega`.

--------------------------------------------------

Milestone 4 — Disjunctive goals
---------------------------------
New capability:
Prove disjunctive goals:

    (x : ℤ) → x > 0 ∨ x ≤ 0
    (a b : ℕ) → a + 2 * b = 8 ∨ 2 * a + b = 8 → a + b ≤ 8

Implementation:
- Use `by_cases` or `omega` directly (omega handles disjunctions in ℤ).
- For implications with disjunctive hypotheses, use `rcases` to split.

--------------------------------------------------

Milestone 5 — Negations
-------------------------
New capability:
Handle goals with negation and inequality of the form `¬(p)`:

    ¬(x = y ∧ x ≠ y)
    (x y : ℤ) → ¬(x < y ∧ y < x)

Implementation:
- Push negation inward with `push_neg`.
- Dispatch to `omega` on the resulting linear goal.

--------------------------------------------------

Milestone 6 — Simple existential witnesses
-------------------------------------------
New capability:
Prove existential goals where the witness is directly computable:

    (n : ℕ) → n > 0 → ∃ k : ℕ, k ≤ n ∧ 2 * k ≥ n
    ∃ x : ℤ, 2 * x + 1 = 7

Implementation:
- Use `omega` for closed goals (no free variables).
- For goals with free variables, use Fourier-Motzkin projection to find a witness
  expression, then `exact ⟨witness, by omega⟩`.

--------------------------------------------------

Milestone 7 — Existential elimination in hypotheses
----------------------------------------------------
New capability:
Use existential hypotheses in proofs:

    (n : ℕ) → (∃ x : ℕ, 2 * x + 1 = n) → n % 2 = 1

Implementation:
- Use `obtain ⟨x, hx⟩ := h` to extract the witness.
- Dispatch the remaining linear goal to `omega`.

--------------------------------------------------

Milestone 8 — Natural number subtraction and coercions
-------------------------------------------------------
New capability:
Handle goals with natural number subtraction and ℕ → ℤ coercions:

    (n m : ℕ) → n ≥ m → n - m + m = n
    (n : ℕ) → (↑n : ℤ) + 1 > 0

Implementation:
- Use `omega` which handles ℕ subtraction.
- For coercions `↑n`, use `push_cast` before dispatching.

Key lemma:
- `Nat.cast_nonneg`, `Int.ofNat_nonneg`

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Non-linear terms**: Detect and fail with "presburger: non-linear term `x * y`".
2. **Universal quantifiers**: Fail with "presburger: use `omega` for ∀ goals".
3. **Unsupported types**: Fail for ℝ or ℚ goals.
4. **Complexity bounds**: Abort if the constraint system has > 20 variables or
   > 50 inequalities (to prevent infinite loops).

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
isLinear      : Expr → Bool
normalizeGoal : Expr → TacticM Expr    -- push_neg, push_cast, intro
dispatchOmega : TacticM Unit
findWitness   : Expr → TacticM Expr    -- for existential goals
```

Also add trace option `trace.presburger` printing:
- detected goal fragment (QF-linear, existential, etc.)
- normalization steps applied
- backend tactic used

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Linearity check, principled failure |
| 2 | Atomic constraints | Direct `omega` dispatch |
| 3 | Conjunction / implication | `intro` + `omega` |
| 4 | Disjunctions | `by_cases` + `omega` |
| 5 | Negations | `push_neg` + `omega` |
| 6 | Existential witnesses | Witness computation + `omega` |
| 7 | Existential hypotheses | `obtain` + `omega` |
| 8 | ℕ subtraction / coercions | `push_cast` + `omega` |
| 9 | Guardrails | Non-linear, universal, type checks |
| 10 | Refactor | Clean architecture + tracing |
