norm_num_bounds — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `norm_num_bounds` that proves numerical bound goals of
the form `a < E` and `a < E < b` (and `≤` variants) for real-valued expressions
involving constants, arithmetic, and transcendental functions. Each milestone strictly
refines the previous one: it handles a wider class of expressions, never weakening
earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic evaluation order.
3. Conservative bounds: never claim a bound that is not rigorously justified.
4. Delegation to `norm_num` for rational arithmetic and to Mathlib's known bounds for
   transcendental constants.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `a < E`, `E < b`, `a < E < b`, `a ≤ E ≤ b`, and mixed.
- If the goal shape is not a numerical bound, fail with "norm_num_bounds: unsupported goal".
- Extract the expression `E` and the rational bounds `a`, `b`.

Architecture (future-proof):
- parse goal shape
- evaluate E with interval arithmetic
- verify bounds
- construct proof term
- fail with informative message

--------------------------------------------------

Milestone 2 — Rational arithmetic
-----------------------------------
New capability:
Prove bounds for rational expressions:

    (3 : ℚ) < (7 : ℝ) / 2
    (7 : ℝ) / 2 < (4 : ℚ)

Implementation:
- Dispatch to `norm_num` for goals where `E` is a rational expression.
- Handle the two-sided form by splitting into two one-sided goals.

--------------------------------------------------

Milestone 3 — Known bounds for π and e
----------------------------------------
New capability:
Prove bounds for the transcendental constants π and e:

    (3.14 : ℚ) < π ∧ π < (3.15 : ℚ)
    (2.71 : ℚ) < Real.exp 1 ∧ Real.exp 1 < (2.72 : ℚ)

Implementation:
- Use Mathlib's `Real.pi_gt_3141592` and `Real.pi_lt_315` (or equivalent).
- Use known bounds for `Real.exp 1` from `Mathlib.Analysis.SpecialFunctions.Exp`.
- Prove each half separately with `linarith` + known bounds.

Key lemmas:
- `Real.pi_gt_3141592`, `Real.pi_lt_3141593`
- Bounds on `Real.exp 1` from Mathlib

--------------------------------------------------

Milestone 4 — Natural logarithm bounds
----------------------------------------
New capability:
Prove bounds for `Real.log` at rational arguments:

    (0.69 : ℚ) < Real.log 2 ∧ Real.log 2 < (0.70 : ℚ)
    (1.09 : ℚ) < Real.log 3 ∧ Real.log 3 < (1.10 : ℚ)

Implementation:
- Use Mathlib's existing log bounds (e.g., `Real.log_two_gt_d9`).
- For other arguments, derive bounds from known values using `Real.log_le_log`.
- Extend with small lookup table for log at integers 2–10.

--------------------------------------------------

Milestone 5 — Arithmetic operations on bounded expressions
-----------------------------------------------------------
New capability:
Propagate bounds through `+`, `-`, `*`, `/`:

    (6.28 : ℚ) < 2 * π ∧ 2 * π < (6.29 : ℚ)
    (4.81 : ℚ) < Real.log 2 + π + 1/2 ∧ ... < (4.82 : ℚ)

Implementation:
- Interval arithmetic: `[l₁, u₁] + [l₂, u₂] = [l₁ + l₂, u₁ + u₂]`.
- Multiplication: handle sign cases.
- Use `linarith` to close the final numerical comparison.

--------------------------------------------------

Milestone 6 — Square root bounds
----------------------------------
New capability:
Prove bounds for `Real.sqrt`:

    (1.41 : ℚ) < Real.sqrt 2 ∧ Real.sqrt 2 < (1.42 : ℚ)

Implementation:
- Use `Real.sq_sqrt` and `Real.sqrt_lt'` to reduce to algebraic bounds.
- Apply `norm_num` to verify the squared bound.

Key lemmas:
- `Real.sqrt_lt_sqrt`, `Real.sqrt_le_sqrt`
- `Real.sq_sqrt` : `0 ≤ x → Real.sqrt x ^ 2 = x`

--------------------------------------------------

Milestone 7 — Exponential and log compositions
-----------------------------------------------
New capability:
Handle composed expressions:

    (1.76 : ℚ) < Real.exp (Real.log 2 + Real.log 3) ∧ ... < (1.77 : ℚ)

Implementation:
- Use `Real.exp_add`, `Real.exp_log` to simplify compositions.
- Propagate interval bounds through exp using `Real.exp_le_exp`.

--------------------------------------------------

Milestone 8 — Integer powers
------------------------------
New capability:
Prove bounds for `E ^ n` with `n : ℕ`:

    (1.99 : ℚ) < Real.sqrt 2 ^ 2 ∧ Real.sqrt 2 ^ 2 < (2.01 : ℚ)

Implementation:
- Use interval exponentiation: `[l, u] ^ n` via `pow_le_pow_left`.
- Handle even/odd exponents separately for sign analysis.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Domain violations**: Fail for `log(x)` with `x ≤ 0`, `sqrt(x)` with `x < 0`.
2. **Division by zero**: Reject denominators whose interval contains 0.
3. **Precision limit**: Fail gracefully when required margin is too thin.
4. **Unsupported functions**: `sin`, `cos`, `tan` not yet supported — fail clearly.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
evalInterval  : Expr → TacticM (ℚ × ℚ)   -- lower, upper
verifyBound   : ℚ → ℚ × ℚ → BoundKind → TacticM Unit
buildProof    : Expr → ℚ × ℚ → TacticM Unit
```

Also add trace option `trace.norm_num_bounds` printing:
- evaluated interval for each subexpression
- Mathlib lemmas used
- final bound check

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Goal parsing, principled failure |
| 2 | Rational arithmetic | `norm_num` dispatch |
| 3 | π and e | Transcendental constant bounds |
| 4 | log bounds | `log 2`, `log 3`, etc. |
| 5 | Arithmetic ops | Interval arithmetic for +, -, *, / |
| 6 | sqrt | Square root bounds |
| 7 | exp / log compositions | Composed expressions |
| 8 | Integer powers | `E ^ n` bounds |
| 9 | Guardrails | Domain checks, precision limits |
| 10 | Refactor | Clean architecture + tracing |
