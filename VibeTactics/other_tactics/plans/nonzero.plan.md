nonzero — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `nonzero` that proves goals of the form `e ≠ 0` using
algebraic lemmas and a positivity fallback. Each milestone strictly refines the previous
one: it handles more expression forms or adds a stronger fallback, never weakening
earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering (structural rules before fallback).
3. Conservative recursion: bound depth to prevent looping.
4. Delegation to `positivity` and `norm_num` as backends.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- If the goal is not of the form `e ≠ 0`, fail with a clear message.
- Detect goals syntactically matching `_ ≠ 0` or `¬(_ = 0)`.
- If the expression is not in a supported algebraic structure, fail with
  "nonzero: unsupported goal".

Architecture (future-proof):
- match goal shape
- pattern-match on expression form
- apply rule or fallback
- fail with informative message

--------------------------------------------------

Milestone 2 — Nonzero numeric literals
---------------------------------------
New capability:
Prove that numeric literals are nonzero:

    (1 : ℤ) ≠ 0
    (2 : ℚ) ≠ 0
    (-3 : ℝ) ≠ 0

Implementation:
- Recognise numeric literal expressions.
- Dispatch to `norm_num` for the decision.
- Handle both positive and negative literals.

--------------------------------------------------

Milestone 3 — Hypothesis lookup
---------------------------------
New capability:
Use local hypotheses of the form `h : a ≠ 0`:

    example (a : ℤ) (ha : a ≠ 0) : a ≠ 0 := by nonzero

Implementation:
- Search the local context for a hypothesis matching `?e ≠ 0`.
- Apply it directly if found.
- This is the base case for the recursive rules below.

--------------------------------------------------

Milestone 4 — Negation rule
-----------------------------
New capability:
Prove that negating a nonzero element is nonzero:

    example (a : ℤ) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

Key lemma:
- `neg_ne_zero.mpr` : `a ≠ 0 → -a ≠ 0`

Implementation:
- Detect `e = -f`.
- Recursively prove `f ≠ 0`.
- Apply `neg_ne_zero.mpr`.

--------------------------------------------------

Milestone 5 — Multiplication rule
-----------------------------------
New capability:
Prove that a product of nonzero elements is nonzero:

    example (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

Key lemma:
- `mul_ne_zero` : `a ≠ 0 → b ≠ 0 → a * b ≠ 0`

Implementation:
- Detect `e = f * g`.
- Recursively prove `f ≠ 0` and `g ≠ 0`.
- Apply `mul_ne_zero`.

--------------------------------------------------

Milestone 6 — Power rule
--------------------------
New capability:
Prove that a power with positive exponent is nonzero:

    example (a : ℤ) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero
    example (a : ℝ) (ha : a ≠ 0) : a ^ 2 ≠ 0 := by nonzero

Key lemma:
- `pow_ne_zero` : `a ≠ 0 → n > 0 → a ^ n ≠ 0`

Implementation:
- Detect `e = f ^ n` where `n` is a literal or provably positive.
- Recursively prove `f ≠ 0`.
- Apply `pow_ne_zero`.

--------------------------------------------------

Milestone 7 — Positivity fallback
-----------------------------------
New capability:
For additive expressions or other unsupported forms, fall back to `positivity`:

    example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a + b ≠ 0 := by nonzero

Implementation:
- When structural rules do not apply and a `PartialOrder` instance is available,
  attempt to prove `0 < e` using the `positivity` tactic.
- If `positivity` succeeds, apply `ne_of_gt`.

--------------------------------------------------

Milestone 8 — simp normalization pre-pass
------------------------------------------
Before dispatching structural rules, run a lightweight normalization step.

Goals:
- Unfold definitional equalities that hide the expression structure.
- Normalise `(-(-a))` → `a`, `a * 1` → `a`, etc.

Implementation:
- Run `simp only [neg_neg, mul_one, one_mul, pow_zero, pow_one]` on the expression.
- Then retry the structural rules.

--------------------------------------------------

Milestone 9 — Guardrails and complexity bounds
----------------------------------------------
Add safety checks:

1. **Recursion depth**: Limit structural recursion to depth 10.
2. **Missing instances**: Fail clearly when `Zero`, `Neg`, `Mul`, `Pow` unavailable.
3. **Zero expression**: `0 ≠ 0` should fail with an informative message.
4. **Unclear exponents**: `a ^ b` where `b` is not a literal or provably positive
   should fall back to `positivity` or fail clearly.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
proveNonzero  : Expr → Nat → TacticM Unit   -- depth-limited
tryPositivity : Expr → TacticM Unit
normalizeExpr : Expr → TacticM Expr
```

Also add trace option `trace.nonzero` printing:
- matched expression pattern
- recursive subgoals
- applied lemma

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Principled failure |
| 2 | Literals | `(2 : ℤ) ≠ 0` |
| 3 | Hypotheses | Local `h : a ≠ 0` |
| 4 | Negation | `-a ≠ 0` |
| 5 | Multiplication | `a * b ≠ 0` |
| 6 | Powers | `a ^ n ≠ 0` |
| 7 | Positivity fallback | `a + b ≠ 0` via `positivity` |
| 8 | simp pre-pass | Normalization before dispatch |
| 9 | Guardrails | Depth limit, clear errors |
| 10 | Refactor | Clean architecture + tracing |
