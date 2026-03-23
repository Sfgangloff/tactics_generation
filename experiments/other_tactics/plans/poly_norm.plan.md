poly_norm — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `poly_norm` that decides polynomial equality goals
`p = q` by normalizing both sides to canonical form (sum of monomials sorted by
degree with like terms combined). Each milestone strictly refines the previous one:
it handles more polynomial expression forms, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic normalization (canonical form is unique).
3. Conservative expansion: expand only as much as needed.
4. Delegation to `ring` whenever the goal is within its reach, and to `norm_num`
   for coefficient arithmetic.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `p = q` where `p q : Polynomial ℚ` (or ℤ, ℝ).
- If the goal is not a polynomial equality, fail with "poly_norm: unsupported goal".
- If either side contains non-polynomial operations (division, transcendental
  functions), fail with "poly_norm: non-polynomial expression".

Architecture (future-proof):
- check goal shape
- parse both sides as polynomial expressions
- normalize each side
- compare normalized forms
- fail informatively

--------------------------------------------------

Milestone 2 — Reflexivity and constant equalities
--------------------------------------------------
New capability:
Prove trivial equalities:

    (x : ℚ) = x
    (3 : ℚ[X]) = (3 : ℚ[X])
    (0 : ℚ[X]) = 0

Implementation:
- Normalise both sides; if syntactically identical after `ring_nf`, close with `rfl`.
- Use `ring` as the first fallback for ground equalities.

--------------------------------------------------

Milestone 3 — Addition and like-terms collection
-------------------------------------------------
New capability:
Prove equalities that require collecting like terms:

    (x : ℚ) + x = 2 * x
    3 * x ^ 2 - x ^ 2 = 2 * x ^ 2
    (1/2 : ℚ) * x + (3/2) * x = 2 * x

Implementation:
- Use `ring_nf` to expand and collect.
- Close with `ring`.

--------------------------------------------------

Milestone 4 — Polynomial expansion
-------------------------------------
New capability:
Prove equalities requiring expansion:

    ((x : ℚ) + 1) ^ 2 = x ^ 2 + 2 * x + 1
    ((x : ℚ) - 2) ^ 2 = x ^ 2 - 4 * x + 4
    ((x : ℚ) + 1) * (x - 1) = x ^ 2 - 1

Implementation:
- Expand the LHS or RHS with `ring_nf`.
- Close with `ring`.

At this point the tactic is essentially `ring` with extra parsing; subsequent
milestones add capability beyond what `ring` can do directly.

--------------------------------------------------

Milestone 5 — Normalization check with `decide`
------------------------------------------------
New capability:
For polynomials over ℤ or ℚ with concrete coefficients, use `decide` after reducing
to a computable form:

    Polynomial.C 3 * X ^ 2 + Polynomial.C 2 * X = Polynomial.C 3 * X ^ 2 + Polynomial.C 2 * X

Implementation:
- When all coefficients are concrete rationals and degree is bounded (≤ 6), attempt
  to convert to `decide`-friendly form using `Polynomial.ext_iff` and coefficient
  evaluation.

--------------------------------------------------

Milestone 6 — Coefficient-based proof
---------------------------------------
New capability:
Prove equalities by comparing coefficients:

    Polynomial.coeff (x ^ 2 + 2 * x + 1 : ℤ[X]) 0 = Polynomial.coeff ((x+1)^2 : ℤ[X]) 0

Implementation:
- Apply `Polynomial.ext` to reduce to coefficient equality.
- Use `simp [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_pow]`.
- Close each coefficient goal with `norm_num` or `ring`.

--------------------------------------------------

Milestone 7 — Zero-equality `p - q = 0`
-----------------------------------------
New capability:
Prove that two polynomials are equal by showing their difference is zero:

    (x : ℚ) ^ 2 - 2 * x + 1 - (x - 1) ^ 2 = 0

Implementation:
- Recognise `p - q = 0` as equivalent to `p = q`.
- Normalise using `ring_nf` and close with `ring`.

--------------------------------------------------

Milestone 8 — Multivariate support (limited)
---------------------------------------------
New capability:
Handle two-variable polynomial equalities:

    (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2

Implementation:
- Widen the parser to accept two-variable expressions.
- Dispatch to `ring` for all such goals.

Note: True multivariate normalization is not implemented; `ring` handles these goals.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Division**: Reject `p / q` with a clear message.
2. **Non-polynomial subexpressions**: Reject `Real.sqrt x`, `Real.exp x`, etc.
3. **Degree overflow**: Warn when normalised degree > 10 (may be slow).
4. **Type mismatch**: Fail clearly when the two sides have incompatible types.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
isPolynomialExpr  : Expr → Bool
normalizeToCanon  : Expr → TacticM Expr   -- ring_nf + collect
comparePolys      : Expr → Expr → TacticM Bool
```

Also add trace option `trace.poly_norm` printing:
- detected polynomial expression forms
- normalized LHS and RHS
- comparison result

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Non-polynomial check, principled failure |
| 2 | Reflexivity / constants | `rfl` and `ring` dispatch |
| 3 | Like-term collection | `ring_nf` + `ring` |
| 4 | Expansion | `(x+1)^2 = x^2+2x+1` |
| 5 | decide-based proof | Concrete coefficient polynomials |
| 6 | Coefficient-based proof | `Polynomial.ext` + `simp` |
| 7 | Zero-equality form | `p - q = 0` |
| 8 | Two-variable support | `ring` dispatch |
| 9 | Guardrails | Division, non-poly, type mismatch |
| 10 | Refactor | Clean architecture + tracing |
