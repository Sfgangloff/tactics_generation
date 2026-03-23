simp_leading_coeff — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `simp_leading_coeff` that proves goals of the form
`Polynomial.leadingCoeff p = c` by extracting and simplifying the leading coefficient
of `p`. Each milestone strictly refines the previous one: it handles more polynomial
forms, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic degree computation.
3. Conservative coefficient extraction: do not assume nonzero coefficients unless stated.
4. Delegation to `norm_num` for coefficient arithmetic and `simp` for polynomial rewrites.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `Polynomial.leadingCoeff p = c`.
- Also detect goals where `leadingCoeff p` appears as a sub-expression.
- If the goal does not match, fail with "simp_leading_coeff: unsupported goal".

Architecture (future-proof):
- match goal pattern
- parse polynomial expression
- compute degree and leading coefficient
- compare with `c`
- fail informatively

--------------------------------------------------

Milestone 2 — Zero polynomial
-------------------------------
New capability:
Prove the leading coefficient of the zero polynomial:

    Polynomial.leadingCoeff (0 : ℤ[X]) = 0

Key lemma:
- `Polynomial.leadingCoeff_zero` : `leadingCoeff 0 = 0`

Implementation:
- Recognise `p = 0` syntactically.
- Apply `Polynomial.leadingCoeff_zero` and close with `rfl`.

--------------------------------------------------

Milestone 3 — Constant polynomial C c
----------------------------------------
New capability:
Prove the leading coefficient of a constant polynomial:

    Polynomial.leadingCoeff (Polynomial.C 42 : ℤ[X]) = 42
    Polynomial.leadingCoeff (Polynomial.C (1/2) : ℚ[X]) = 1/2

Key lemma:
- `Polynomial.leadingCoeff_C` : `leadingCoeff (C a) = a`

Implementation:
- Recognise `Polynomial.C c` syntactically.
- Apply `Polynomial.leadingCoeff_C` and close with `norm_num` or `rfl`.

--------------------------------------------------

Milestone 4 — Monomials X ^ n and C c * X ^ n
-----------------------------------------------
New capability:
Prove leading coefficients for monomials:

    Polynomial.leadingCoeff (X ^ 3 : ℤ[X]) = 1
    Polynomial.leadingCoeff (3 * X ^ 2 : ℚ[X]) = 3
    Polynomial.leadingCoeff (Polynomial.C a * X ^ 2 : ℝ[X]) = a

Key lemmas:
- `Polynomial.leadingCoeff_X_pow` : `leadingCoeff (X^n) = 1`
- `Polynomial.leadingCoeff_C_mul_X_pow` (or derive via `mul_comm` + `leadingCoeff_mul`)

Implementation:
- Recognise `C c * X ^ n`, `X ^ n`, `X` patterns.
- Apply corresponding lemmas.

--------------------------------------------------

Milestone 5 — Simple sums with clear leading term
--------------------------------------------------
New capability:
Prove leading coefficients for sums where the leading term is obvious:

    Polynomial.leadingCoeff (X ^ 3 + 2 * X + 1 : ℤ[X]) = 1
    Polynomial.leadingCoeff (3 * X ^ 2 + X + 5 : ℚ[X]) = 3

Implementation:
- Use `simp only [Polynomial.leadingCoeff_add_of_degree_lt]` when the degree of
  the second summand is strictly less than the first.
- Need to verify degree inequality: use `Polynomial.degree_C_mul_X_pow_le` etc.

Key lemma:
- `Polynomial.leadingCoeff_add_of_degree_lt`

--------------------------------------------------

Milestone 6 — Products of polynomials
---------------------------------------
New capability:
Prove that the leading coefficient of a product is the product of leading coefficients:

    Polynomial.leadingCoeff ((X + 1) * (X ^ 2 + 2) : ℤ[X]) = 1

Key lemma:
- `Polynomial.leadingCoeff_mul` : `leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q`
  (when the ring is an integral domain, or when leading coefficients are nonzero)

Implementation:
- Recursively extract leading coefficients of each factor.
- Multiply with `norm_num`.

--------------------------------------------------

Milestone 7 — Symbolic coefficient expressions
------------------------------------------------
New capability:
Handle symbolic (variable) leading coefficients:

    (a : ℝ) : Polynomial.leadingCoeff (a * X ^ 2 + X + 1 : ℝ[X]) = a
    (c : ℤ) : Polynomial.leadingCoeff (c * X ^ 3 + X + 2 : ℤ[X]) = c

Implementation:
- When the leading coefficient is a variable rather than a literal, apply
  `Polynomial.leadingCoeff_add_of_degree_lt` and leave the result as `a` or `c`.
- No norm_num needed; `rfl` or `simp` closes the goal.

--------------------------------------------------

Milestone 8 — Monomial constructor form
-----------------------------------------
New capability:
Handle `Polynomial.monomial n c` expressions:

    Polynomial.leadingCoeff (Polynomial.monomial 3 5 + Polynomial.monomial 1 2 : ℕ[X]) = 5

Key lemma:
- `Polynomial.leadingCoeff_monomial` : `leadingCoeff (monomial n a) = a` when `n` is
  the degree

Implementation:
- Recognise `Polynomial.monomial n c` patterns.
- Compare degrees, apply `leadingCoeff_monomial` for the highest-degree term.

--------------------------------------------------

Milestone 9 — Guardrails and edge cases
-----------------------------------------
Add safety checks:

1. **Same-degree summands**: Warn when two summands have the same degree and leading
   coefficients may cancel.
2. **Integral domain requirement**: Some leading coefficient lemmas require `IsDomain`;
   fail clearly when the instance is missing.
3. **Degree overflow**: Reject polynomials with degree > 20 in combined form.
4. **Abstract polynomial**: If polynomial expression cannot be structurally analysed,
   fall back to `simp [Polynomial.leadingCoeff]` and report if it fails.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
computeDegree      : Expr → TacticM ℕ
extractLeadingTerm : Expr → TacticM Expr   -- the leading monomial
proveLeadingCoeff  : Expr → Expr → TacticM Unit
```

Also add trace option `trace.simp_leading_coeff` printing:
- computed degree
- identified leading term
- applied lemmas

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Goal parsing, principled failure |
| 2 | Zero polynomial | `leadingCoeff 0 = 0` |
| 3 | Constant `C c` | `leadingCoeff (C a) = a` |
| 4 | Monomials | `X^n`, `C c * X^n` |
| 5 | Sums | Leading term dominates |
| 6 | Products | `leadingCoeff (p * q)` |
| 7 | Symbolic coefficients | Variable leading coeff |
| 8 | `monomial` constructor | `Polynomial.monomial n c` |
| 9 | Guardrails | Cancellation, domain instances |
| 10 | Refactor | Clean architecture + tracing |
