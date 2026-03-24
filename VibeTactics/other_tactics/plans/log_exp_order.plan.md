log_exp_order — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `log_exp_order` that proves asymptotic ordering goals
of the form `∀ᶠ x in Filter.atTop, f x ⋄ g x` where `f` and `g` are built from
logarithms, exponentials, polynomials, and constants. Each milestone strictly refines
the previous one: it handles a larger fragment of the asymptotic hierarchy, never
weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering (most-specific first).
3. Conservative growth-rate assignment.
4. Delegation to existing Mathlib lemmas for each comparison step.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- If the goal is not of the form `∀ᶠ x in Filter.atTop, f x ⋄ g x`, fail clearly.
- Detect the filter quantifier and the comparison operator.
- If the expression shape is unsupported, fail with "log_exp_order: unsupported goal".

Architecture (future-proof):
- match goal shape
- classify LHS and RHS growth rates
- look up comparison in hierarchy
- construct proof
- fail with informative message

--------------------------------------------------

Milestone 2 — Constant vs positive power
------------------------------------------
New capability:
Prove that any positive polynomial power eventually dominates a positive constant:

    ∀ᶠ x in Filter.atTop, (1 : ℝ) < x
    ∀ᶠ x in Filter.atTop, (2 : ℝ) ≤ x ^ 2

Implementation:
- Recognise constant expressions and `x ^ n` for literal `n > 0`.
- Use `Filter.eventually_gt_atTop` and `Filter.Tendsto.eventually_ge_atTop`.
- Handle `<` and `≤` variants.

--------------------------------------------------

Milestone 3 — Polynomial hierarchy
-------------------------------------
New capability:
Prove ordering between polynomial powers:

    ∀ᶠ x in Filter.atTop, x ^ 2 < x ^ 3
    ∀ᶠ x in Filter.atTop, x ≤ x ^ 2

Implementation:
- Assign each `x ^ a` a real exponent `a`.
- Compare exponents; use Mathlib's `eventually_pow_lt_pow_of_lt` family.
- Handle fractional exponents `x ^ (1/2 : ℝ)` via `Real.rpow`.

--------------------------------------------------

Milestone 4 — Logarithm below polynomial
------------------------------------------
New capability:
Prove that log grows slower than any positive power:

    ∀ᶠ x in Filter.atTop, Real.log x < x ^ (1/2 : ℝ)
    ∀ᶠ x in Filter.atTop, Real.log x ^ 3 < x

Key lemmas:
- `Real.isLittleO_log_rpow` : `log = o(x^ε)` for any `ε > 0`.

Implementation:
- Classify one side as `log^k x` and the other as `x^a` with `a > 0`.
- Apply transitivity if needed (e.g., `log x < log^2 x` within log powers).

--------------------------------------------------

Milestone 5 — Exponential above polynomial
-------------------------------------------
New capability:
Prove that `exp x` dominates any polynomial:

    ∀ᶠ x in Filter.atTop, x ^ 3 < Real.exp x
    ∀ᶠ x in Filter.atTop, x ^ 100 ≤ Real.exp x

Key lemmas:
- `Real.isLittleO_pow_exp_atTop` : `x^n = o(exp x)`.

--------------------------------------------------

Milestone 6 — Products and scalar multiples
--------------------------------------------
New capability:
Handle expressions with scalar factors and products:

    ∀ᶠ x in Filter.atTop, 2 * x ^ 2 ≤ Real.exp x
    ∀ᶠ x in Filter.atTop, x ^ 2 * Real.log x < Real.exp x

Implementation:
- Strip positive constant factors (they do not affect growth rate).
- Classify `x^a * log^k x` as growth rate `poly_pos a` (dominant term).
- Use `IsLittleO` composition rules.

--------------------------------------------------

Milestone 7 — Nested logarithms and double exponential
-------------------------------------------------------
New capability:
Handle iterated log/exp:

    ∀ᶠ x in Filter.atTop, Real.log (Real.log x) < Real.log x
    ∀ᶠ x in Filter.atTop, Real.exp x < Real.exp (Real.exp x)

Implementation:
- Extend the hierarchy to include `log∘log`, `exp∘exp` levels.
- Use `Filter.Tendsto.comp` for composed limits.
- Bound nesting depth to 3 to prevent infinite regress.

--------------------------------------------------

Milestone 8 — Sums dominated by their largest term
----------------------------------------------------
New capability:
Handle sums where one term dominates:

    ∀ᶠ x in Filter.atTop, 2 * x ^ 2 + 3 * x + Real.log x ≤ x ^ 3

Implementation:
- Normalise both sides: identify the dominant growth class.
- Reduce to a comparison of dominant terms.
- Use `Filter.Eventually.add` and triangle-inequality style arguments.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Unsupported functions**: Fail for `sin`, `cos`, `abs`, etc.
2. **Non-eventually-positive**: Reject expressions that can be negative for large x.
3. **Incomparable growth rates**: Fail clearly for oscillatory or undefined comparisons.
4. **Complexity bound**: Reject expressions with nesting depth > 4.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
classifyGrowth   : Expr → TacticM GrowthClass
compareGrowth    : GrowthClass → GrowthClass → TacticM Ordering
buildProof       : GrowthClass → GrowthClass → CompOp → TacticM Unit
```

where `GrowthClass` is:
```lean
inductive GrowthClass where
  | constant | logPower (k : ℕ) | polyPos (a : ℚ) | exp | doubleExp
```

Also add trace option `trace.log_exp_order`.

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Principled failure |
| 2 | Const vs poly | `1 < x`, `c ≤ x^n` |
| 3 | Poly hierarchy | `x^a < x^b` |
| 4 | Log below poly | `log x < x^ε` |
| 5 | Exp above poly | `x^n < exp x` |
| 6 | Products / scalars | `c * x^a * log^k x` |
| 7 | Nested log/exp | `log(log x)`, `exp(exp x)` |
| 8 | Sums | Dominant-term reduction |
| 9 | Guardrails | Unsupported / incomparable |
| 10 | Refactor | Clean architecture + tracing |
