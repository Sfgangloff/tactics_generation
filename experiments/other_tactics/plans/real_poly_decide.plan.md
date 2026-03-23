real_poly_decide — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `real_poly_decide` that decides quantifier-free
polynomial statements over ℝ: equations, inequalities, and Boolean combinations
thereof. Each milestone strictly refines the previous one: it handles a larger
fragment of real polynomial arithmetic, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering (tautologies first, sign analysis last).
3. Conservative sign assignment: only assert what is provably true.
4. Delegation to existing tactics (`ring`, `nlinarith`, `norm_num`, `polyrith`)
   where applicable.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals that are quantifier-free Boolean combinations of polynomial
  comparisons over ℝ.
- If non-polynomial expressions are present (`Real.sin`, `Real.exp`, etc.), fail.
- If quantifiers are present, fail with "real_poly_decide: quantifiers not supported".

Architecture (future-proof):
- check for non-polynomial terms
- normalize atomic comparisons
- dispatch to rule engine
- fail informatively

--------------------------------------------------

Milestone 2 — Tautologies via ring
------------------------------------
New capability:
Prove polynomial equalities that hold by ring axioms:

    ∀ x : ℝ, (x - 1) ^ 2 = x ^ 2 - 2 * x + 1
    ∀ x y : ℝ, (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2

Implementation:
- Dispatch directly to `ring` for goals that are universally quantified equalities.
- Recognise the `∀ x₁ ... xₙ : ℝ, lhs = rhs` pattern.

--------------------------------------------------

Milestone 3 — Non-negative sum-of-squares
-------------------------------------------
New capability:
Prove that sum-of-squares expressions are non-negative:

    ∀ x : ℝ, x ^ 2 ≥ 0
    ∀ x y : ℝ, x ^ 2 + y ^ 2 ≥ 0

Implementation:
- Recognise expressions of the form `∑ eᵢ ^ 2 ≥ 0`.
- Apply `sq_nonneg` and `add_nonneg` iteratively.
- Fall back to `nlinarith [sq_nonneg x, sq_nonneg y, ...]`.

Key lemma: `sq_nonneg`

--------------------------------------------------

Milestone 4 — Disjunctive tautologies
---------------------------------------
New capability:
Prove excluded-middle style disjunctions:

    ∀ x : ℝ, x > 0 ∨ x ≤ 0
    ∀ x y : ℝ, x ^ 2 + y ^ 2 > 0 ∨ (x = 0 ∧ y = 0)

Implementation:
- Use `by_cases h : x > 0` to split.
- Close each branch with `linarith` or `nlinarith`.

--------------------------------------------------

Milestone 5 — Conditional polynomial inequalities
---------------------------------------------------
New capability:
Prove polynomial inequalities under hypotheses:

    ∀ x : ℝ, x > 1 → x ^ 2 > 1
    ∀ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y = 0 → x = 0 ∧ y = 0

Implementation:
- Introduce hypotheses with `intro` / `obtain`.
- Apply `nlinarith` with the hypotheses and squares as hints.

--------------------------------------------------

Milestone 6 — Polynomial factorization equalities
---------------------------------------------------
New capability:
Prove biconditionals via factorization:

    ∀ x : ℝ, x ^ 2 - 4 = 0 ↔ (x = 2 ∨ x = -2)
    ∀ x : ℝ, (x ^ 3 - x = 0) ↔ (x = 0 ∨ x = 1 ∨ x = -1)

Implementation:
- For `p = 0 ↔ (x = r₁ ∨ ... ∨ x = rₙ)`: introduce both directions.
  - Forward: use `have := factor_lemma; nlinarith`.
  - Backward: substitute `x = rᵢ` and use `ring` / `norm_num`.

--------------------------------------------------

Milestone 7 — AM-GM and classical inequalities
------------------------------------------------
New capability:
Prove classical polynomial inequalities:

    ∀ x y : ℝ, (x + y) ^ 2 ≥ 4 * x * y
    ∀ x y : ℝ, x ^ 2 + y ^ 2 ≥ 2 * x * y

Implementation:
- Reduce to `(x - y) ^ 2 ≥ 0` using `nlinarith [sq_nonneg (x - y)]`.
- Build a small library of SOS (sum-of-squares) certificates.

--------------------------------------------------

Milestone 8 — Lookup table for common patterns
------------------------------------------------
Add a cached lookup table for frequently occurring patterns:

1. `p ^ 2 ≥ 0` for any monomial `p`
2. `(p - q) ^ 2 ≥ 0` → `p ^ 2 + q ^ 2 ≥ 2 * p * q`
3. Triangle inequality form: `(p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2)`

Implementation:
- Before running the sign analysis engine, check if the goal matches any
  table entry.
- Return the cached proof if found.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Non-polynomial expressions**: Reject `Real.sqrt`, `Real.exp`, etc.
2. **Degree bounds**: Refuse polynomials of degree > 6 (complexity limit).
3. **Symbolic coefficients**: Accept only rational/integer coefficients.
4. **False goals**: Fail clearly with "real_poly_decide: goal is not universally valid".

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
classifyGoal     : Expr → GoalClass
applyRuleEngine  : GoalClass → TacticM Unit
checkLookupTable : Expr → Option Term
```

where `GoalClass` is:
```lean
inductive GoalClass where
  | ringEquality | sosInequality | conditionalIneq | factorization | unknown
```

Also add trace option `trace.real_poly_decide` printing:
- classified goal type
- applied rule
- nlinarith/ring witness

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Non-polynomial check, principled failure |
| 2 | Ring equalities | `ring` dispatch |
| 3 | Sum-of-squares | `x^2 ≥ 0`, SOS patterns |
| 4 | Disjunctive tautologies | `x > 0 ∨ x ≤ 0` |
| 5 | Conditional inequalities | `x > 1 → x^2 > 1` |
| 6 | Factorization biconditionals | `x^2 - 4 = 0 ↔ ...` |
| 7 | AM-GM and classical ineqs | `nlinarith` with SOS hints |
| 8 | Lookup table | Cached common patterns |
| 9 | Guardrails | Non-polynomial, degree limits |
| 10 | Refactor | Clean architecture + tracing |
