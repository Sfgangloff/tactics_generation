decide_monic — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `decide_monic` that decides goals of the form `Monic p`
(and `¬Monic p`) for univariate polynomials over decidable rings. Each milestone strictly
refines the previous one: it either handles more polynomial forms or improves robustness,
never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering.
3. Conservative coefficient extraction.
4. Delegation to existing tactics (simp, norm_num, decide) when appropriate.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- If the goal is not of the form `Monic p`, fail with a clear message.
- Detect goals of the form `Monic ?p` by pattern matching.
- If the goal shape is unsupported, fail with "decide_monic: unsupported goal shape".

Architecture (future-proof):
- match goal shape
- extract polynomial expression
- dispatch to rule engine
- fail with informative message

This dispatcher remains unchanged throughout the project.

--------------------------------------------------

Milestone 2 — Variable polynomial X is monic
--------------------------------------------
New capability:
Prove that the generator polynomial is monic:

    Monic (X : Polynomial R)
    Monic (X ^ n : Polynomial R)

Implementation:
- Recognise `X` and `X ^ n` syntactically.
- Apply `Polynomial.monic_X` and `Polynomial.monic_pow`.

Important constraints:
- Only handle bare `X` and `X ^ n` initially.
- No additions or scalar multiplications yet.

--------------------------------------------------

Milestone 3 — Constant polynomials
-----------------------------------
New capability:
Decide `Monic (C c)` and `¬Monic (C c)`:

    Monic (C (1 : R))
    ¬Monic (C (2 : R))

Implementation:
- Recognise `C c` syntactically.
- Use `norm_num` / `decide` to check whether `c = 1`.
- Apply `Polynomial.monic_C_iff` or equivalent.

Key lemmas:
- `Polynomial.leadingCoeff_C`
- `Polynomial.monic_iff_leadingCoeff_eq_one`

--------------------------------------------------

Milestone 4 — Monic monomial c * X ^ n
---------------------------------------
New capability:
Decide monomial goals:

    Monic (X ^ 3 + C 2 : Polynomial ℤ)   -- not monic
    Monic (1 * X ^ 2 : Polynomial ℚ)

Implementation:
- Recognise `C c * X ^ n` and `X ^ n` patterns.
- Extract leading coefficient and reduce with `norm_num`.
- Use `Polynomial.monic_iff_leadingCoeff_eq_one`.

--------------------------------------------------

Milestone 5 — Monic sums: leading term is monic
------------------------------------------------
New capability:
Prove that a sum is monic when the highest-degree term is monic:

    Monic (X ^ 3 + 2 * X + 1 : Polynomial ℤ)
    Monic (X ^ 2 + X : Polynomial ℚ)

Implementation:
- Normalize with `ring_nf` / `simp` to surface the leading term.
- Check that the leading coefficient equals 1 using `norm_num`.
- Apply `Polynomial.Monic.add_right` or direct `monic_iff` check.

--------------------------------------------------

Milestone 6 — Products of monic polynomials
--------------------------------------------
New capability:
Prove that a product of monic polynomials is monic:

    Monic ((X + 1) * (X - 1) : Polynomial ℤ)
    Monic ((X + 1) ^ 2 : Polynomial ℚ)

Key lemmas:
- `Polynomial.Monic.mul` : `Monic p → Monic q → Monic (p * q)`
- `Polynomial.Monic.pow` : `Monic p → Monic (p ^ n)`

Implementation:
- Recursively decompose products and powers.
- Each factor must itself be decided monic by the tactic.

--------------------------------------------------

Milestone 7 — Negated goals ¬Monic p
-------------------------------------
New capability:
Disprove monicity when leading coefficient is not 1:

    ¬Monic (2 * X ^ 2 + X + 1 : Polynomial ℤ)
    ¬Monic (0 : Polynomial ℚ)

Implementation:
- Detect goals of the form `¬Monic p`.
- Compute leading coefficient; use `norm_num` to verify it differs from 1.
- Apply `Polynomial.not_monic_zero` for the zero polynomial.
- Use `Polynomial.monic_iff_leadingCoeff_eq_one` negated.

--------------------------------------------------

Milestone 8 — Normalization pass before dispatch
-------------------------------------------------
Before dispatching rules, run a lightweight normalization step.

Goals:
- Reduce polynomial expressions to a form where the leading coefficient is
  syntactically visible.
- Handle `ring_nf` / `simp only [...]` to expand and reorder terms.

Good rewrites:
- Distribute multiplications.
- Collect like terms.
- Sort monomials by degree (descending).

Avoid:
- Unbounded simplification.
- Expanding away structure needed for monic detection.

--------------------------------------------------

Milestone 9 — Guardrails and graceful failure
---------------------------------------------
Add safety checks:

1. **Unsupported types**: Fail if the coefficient ring lacks `DecidableEq`.
2. **Non-computable coefficients**: Fail when `leadingCoeff` cannot be evaluated.
3. **Complexity bounds**: Reject polynomials of degree > 20 or term count > 50.
4. **Unknown ring**: Provide a clear error when instances are missing.

Goal: Users get actionable error messages rather than silent failures.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
extractLeadingCoeff : Expr → TacticM Expr
checkMonic          : Expr → TacticM Bool
applyMonicProof     : Expr → TacticM Unit
```

Also add trace option `trace.decide_monic` printing:
- detected polynomial form
- extracted leading coefficient
- applied rule and lemmas used

--------------------------------------------------

Ordering Discipline
-------------------
Rule priority (most specific to most general):

1. `X` and `X ^ n`   (immediate)
2. Constant `C c`    (norm_num check)
3. Monomial          (leading coeff extraction)
4. Sum               (leading term analysis)
5. Product / power   (recursive decomposition)
6. Negated goal      (leading coeff ≠ 1)
7. Failure           (informative message)

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Principled failure |
| 2 | X is monic | `Monic X`, `Monic (X^n)` |
| 3 | Constants | `Monic (C 1)`, `¬Monic (C 2)` |
| 4 | Monomials | `Monic (c * X^n)` |
| 5 | Monic sums | `Monic (X^n + lower)` |
| 6 | Products | `Monic (p * q)` |
| 7 | Negated goals | `¬Monic p` |
| 8 | Normalization | Leading-term visibility pass |
| 9 | Guardrails | Safety checks and clear errors |
| 10 | Refactor | Clean architecture + tracing |
