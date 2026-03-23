poly_coeff — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `poly_coeff` that proves goals of the form
`Polynomial.coeff p n = c` by evaluating the coefficient of degree `n` in `p`.
Each milestone strictly refines the previous one: it handles more polynomial forms,
never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic evaluation order (structural rules first, simp fallback last).
3. Conservative normalization: do not rewrite unless the goal is improved.
4. Delegation to `norm_num` for coefficient arithmetic and `simp` for cleanup.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `Polynomial.coeff ?p ?n = ?c`.
- If the goal is not in this form, fail with "poly_coeff: unsupported goal shape".
- Extract `p`, `n`, `c` from the goal.

Architecture (future-proof):
- parse goal
- reduce `n` to a concrete ℕ
- evaluate coeff of `p` at `n`
- compare with `c`
- fail informatively

--------------------------------------------------

Milestone 2 — Zero polynomial
-------------------------------
New capability:
Prove that all coefficients of the zero polynomial are zero:

    Polynomial.coeff (0 : ℕ[X]) 5 = 0
    Polynomial.coeff (0 : ℤ[X]) 0 = 0

Key lemma:
- `Polynomial.coeff_zero` : `Polynomial.coeff 0 n = 0`

Implementation:
- Recognise `p = 0` syntactically.
- Apply `Polynomial.coeff_zero` and close with `rfl`.

--------------------------------------------------

Milestone 3 — Constant polynomial C c
----------------------------------------
New capability:
Prove coefficient goals for constant polynomials:

    Polynomial.coeff (Polynomial.C 42 : ℕ[X]) 0 = 42
    Polynomial.coeff (Polynomial.C 7 : ℤ[X]) 3 = 0

Key lemmas:
- `Polynomial.coeff_C_zero` : `Polynomial.coeff (C a) 0 = a`
- `Polynomial.coeff_C_ne_zero` : `n ≠ 0 → Polynomial.coeff (C a) n = 0`

Implementation:
- Recognise `C c` syntactically.
- Dispatch to `coeff_C_zero` or `coeff_C_ne_zero` based on whether `n = 0`.
- Use `norm_num` to decide `n = 0` and to verify `c`.

--------------------------------------------------

Milestone 4 — Variable X and X ^ n
-------------------------------------
New capability:
Prove coefficient goals for the variable and its powers:

    Polynomial.coeff (X : ℕ[X]) 1 = 1
    Polynomial.coeff (X ^ 3 : ℤ[X]) 3 = 1
    Polynomial.coeff (X ^ 3 : ℤ[X]) 2 = 0

Key lemmas:
- `Polynomial.coeff_X_of_ne_one` / `Polynomial.coeff_X_one`
- `Polynomial.coeff_X_pow` : `Polynomial.coeff (X^n) k = if k = n then 1 else 0`

--------------------------------------------------

Milestone 5 — Scalar multiple C c * X ^ n
-------------------------------------------
New capability:
Prove coefficient goals for monomials:

    Polynomial.coeff (3 * X ^ 2 : ℤ[X]) 2 = 3
    Polynomial.coeff (C 5 * X ^ 1 : ℚ[X]) 1 = 5
    Polynomial.coeff (C 5 * X : ℚ[X]) 0 = 0

Implementation:
- Recognise `C c * X ^ n` and `c • X ^ n` patterns.
- Apply `Polynomial.coeff_C_mul` and `Polynomial.coeff_X_pow`.
- Use `norm_num` to evaluate `c * (if k = n then 1 else 0)`.

--------------------------------------------------

Milestone 6 — Sums of polynomials
------------------------------------
New capability:
Prove coefficient goals for sums:

    Polynomial.coeff (X ^ 2 + 3 * X + 7 : ℤ[X]) 1 = 3
    Polynomial.coeff (X ^ 2 + 3 * X + 7 : ℤ[X]) 4 = 0

Key lemma:
- `Polynomial.coeff_add` : `Polynomial.coeff (p + q) n = Polynomial.coeff p n + Polynomial.coeff q n`

Implementation:
- Recursively evaluate coeff of each summand.
- Combine with `Polynomial.coeff_add`.
- Use `norm_num` to compute the resulting sum.

--------------------------------------------------

Milestone 7 — Products and binomial expansions
-----------------------------------------------
New capability:
Prove coefficient goals for products:

    Polynomial.coeff ((X + 1) ^ 3 : ℤ[X]) 2 = 3
    Polynomial.coeff ((X + 1) * (X + 2) : ℤ[X]) 1 = 3

Implementation:
- Use `ring_nf` to expand the product into a sum of monomials.
- Then apply the Milestone 6 strategy.
- Limit to low-degree products to keep term count manageable.

--------------------------------------------------

Milestone 8 — norm_num extension approach
------------------------------------------
Refactor the tactic as a `norm_num` extension so it integrates with the `norm_num`
infrastructure:

- Register coefficient evaluation lemmas as `norm_num` plugins.
- This allows `norm_num` to close coefficient goals directly and compose with other
  `norm_num` extensions.

--------------------------------------------------

Milestone 9 — Guardrails and edge cases
-----------------------------------------
Add safety checks:

1. **Non-concrete degree**: If `n` does not reduce to a literal, fail clearly.
2. **Unsupported ring**: If the coefficient ring lacks computable operations, fail.
3. **Degree too high**: If degree > 20 and the polynomial has symbolic coefficients,
   warn and fall back to `simp`.
4. **Subtraction in ℕ**: Warn and cast to ℤ if natural number subtraction is detected.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
evalCoeff  : Expr → ℕ → TacticM Expr   -- expression for Polynomial.coeff p n
proveCoeff : Expr → ℕ → Expr → TacticM Unit
```

Also add trace option `trace.poly_coeff` printing:
- detected polynomial form
- evaluated coefficient expression
- applied lemmas

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Goal parsing, principled failure |
| 2 | Zero polynomial | `coeff 0 n = 0` |
| 3 | Constant `C c` | `coeff (C a) n` |
| 4 | `X` and `X^n` | `coeff (X^n) k` |
| 5 | Monomials | `coeff (C c * X^n) k` |
| 6 | Sums | `coeff (p + q) n` |
| 7 | Products | `coeff (p * q) n` via `ring_nf` |
| 8 | norm_num extension | Integrate with norm_num |
| 9 | Guardrails | Non-concrete degree, edge cases |
| 10 | Refactor | Clean architecture + tracing |
