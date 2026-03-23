ring_char — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `ring_char` that proves ring equalities by combining
standard ring normalization with the characteristic property `n • x = 0`. Each
milestone strictly refines the previous one: it handles more ring expressions and
more characteristic values, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic rule ordering (characteristic check first, ring fallback last).
3. Conservative normalization: reduce coefficients mod the characteristic.
4. Delegation to `ring` for the characteristic-0 fragment, to `norm_num` for
   coefficient arithmetic, and to `simp` with characteristic lemmas.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `e₁ = e₂` in a ring type `R`.
- Search the local context for a `CharP R n` instance.
- If no characteristic instance is found, delegate to `ring` with a warning.
- If the goal is not an equality, fail with "ring_char: goal is not an equality".

Architecture (future-proof):
- detect CharP instance
- extract characteristic n
- normalize both sides mod n
- compare
- fail informatively

--------------------------------------------------

Milestone 2 — Scalar multiple reduction (linear)
-------------------------------------------------
New capability:
Reduce scalar multiples modulo the characteristic:

    {R : Type*} [Ring R] [CharP R 3] (x : R) : 7 • x = 1 • x
    {R : Type*} [Ring R] [CharP R 2] (x : R) : 4 • x = 0

Implementation:
- Extract numeric coefficient `n` from `n • x`.
- Compute `n % char` using `norm_num`.
- Rewrite `n • x` to `(n % char) • x` using `CharP.cast_eq_zero` and `smul_eq_mul`.
- Close with `ring` if both sides reduce to the same expression.

Key lemmas:
- `CharP.cast_eq_zero` : `(↑n : R) = 0` when `char ∣ n`
- `nsmul_eq_mul` : `n • x = ↑n * x`

--------------------------------------------------

Milestone 3 — Characteristic 2: cross-term elimination
-------------------------------------------------------
New capability:
Prove that cross terms vanish in characteristic 2:

    {R : Type*} [CommRing R] [CharP R 2] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2

Implementation:
- Expand using `ring_nf`.
- Identify cross terms of the form `2 • t` and replace by 0 using `CharP.cast_eq_zero`.
- Close with `ring`.

Key lemma: `CharP.add_pow_char` : `[CharP R p] → (x + y) ^ p = x ^ p + y ^ p`
(use for prime characteristic)

--------------------------------------------------

Milestone 4 — Characteristic 3: cube simplification
----------------------------------------------------
New capability:
Prove identities that use `3 • t = 0`:

    {R : Type*} [Ring R] [CharP R 3] (x : R) : x + x + x + x = x
    {R : Type*} [CommRing R] [CharP R 3] (x y : R) : (x + y) ^ 3 = x ^ 3 + y ^ 3

Implementation:
- Use `CharP.add_pow_char` for the Frobenius endomorphism.
- Reduce `n • x` for any `n` using `n % 3`.

--------------------------------------------------

Milestone 5 — General prime characteristic
-------------------------------------------
New capability:
Handle any prime characteristic `p`:

    {R : Type*} [CommRing R] [CharP R 5] (x : R) : 8 • x = 3 • x
    {R : Type*} [CommRing R] [CharP R 7] (x y : R) : 9 • (x + y) ^ 2 + 14 • x = 2 • (x^2 + 2*x*y + y^2)

Implementation:
- Expand with `ring_nf`.
- Replace all `n • t` with `(n % p) • t` using modular arithmetic.
- Close with `ring`.

--------------------------------------------------

Milestone 6 — Non-commutative rings
--------------------------------------
New capability:
Support `[Ring R]` (not just `[CommRing R]`):

    {R : Type*} [Ring R] [CharP R 2] (x : R) : 4 • x = 0
    {R : Type*} [Ring R] [CharP R 3] (x y : R) : 4 • (x + y) = x + y

Implementation:
- Avoid using `ring` for non-commutative cases; use `CharP` rewrites directly.
- Limit support to linear expressions in non-commutative rings.
- For quadratic and higher, require `CommRing`.

--------------------------------------------------

Milestone 7 — Mixed numeric and symbolic coefficients
------------------------------------------------------
New capability:
Handle expressions mixing numeric literals and symbolic coefficients:

    {R : Type*} [CommRing R] [CharP R 7] (x y z : R) :
      9 • (x + y)^2 + 14 • z = 2 • (x^2 + 2*x*y + y^2)

Implementation:
- After `ring_nf`, all numeric coefficients are explicit.
- Apply `% p` reduction uniformly.
- Use `norm_num` for the arithmetic checks.

--------------------------------------------------

Milestone 8 — Characteristic 0 fallback
-----------------------------------------
New capability:
When the characteristic is 0 or unknown, delegate to `ring`:

    {R : Type*} [CommRing R] [CharP R 0] (x y : R) : (x + y)^2 = x^2 + 2*x*y + y^2

Implementation:
- Detect `CharP R 0` and route to `ring`.
- If no `CharP` instance at all, also route to `ring` with a trace message.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Conflicting CharP instances**: Fail with an informative error.
2. **Unknown characteristic**: If `n` in `CharP R n` is not a literal, fail clearly.
3. **Degree limit**: Warn if polynomial degree > 4 (risk of slow `ring_nf`).
4. **Non-polynomial**: Reject goals involving division or inverses.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
detectChar        : TacticM (Option ℕ)
reduceCoeffMod    : ℕ → Expr → TacticM Expr
normalizeRingChar : ℕ → Expr → TacticM Expr
```

Also add trace option `trace.ring_char` printing:
- detected characteristic
- coefficient reduction steps
- final `ring` call

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | CharP detection, principled failure |
| 2 | Scalar reduction | `n • x → (n % p) • x` |
| 3 | Char 2 cross-terms | `(x+y)^2 = x^2+y^2` |
| 4 | Char 3 cubes | `(x+y)^3 = x^3+y^3` |
| 5 | General prime char | Any prime `p` |
| 6 | Non-commutative rings | `[Ring R]` support |
| 7 | Mixed coefficients | Symbolic + numeric |
| 8 | Char 0 fallback | Delegate to `ring` |
| 9 | Guardrails | Conflicts, unknown char |
| 10 | Refactor | Clean architecture + tracing |
