prove_exists_by_tendsto — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `prove_exists_by_tendsto` that proves goals of the form
`∃ ε > 0, f₁(ε) < δ ∧ f₂(ε) < δ ∧ ...` by showing each function tends to 0 at 0
and extracting a suitable witness. Each milestone strictly refines the previous one:
it handles more function forms and more conjuncts, never weakening earlier behaviour.

We enforce:
1. Monotonic test suite (never delete tests).
2. Deterministic goal decomposition.
3. Conservative limit-proving: use only well-known Mathlib continuity facts.
4. Delegation to `continuity`, `simp`, and filter/topology lemmas.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behaviour:
- Detect goals of the form `∃ ε : ℝ, 0 < ε ∧ P ε`.
- If the goal is not an existential of this form, fail with a clear message.
- Extract the existential variable, the positivity condition, and the body.

Architecture (future-proof):
- match goal: ∃ ε, 0 < ε ∧ body
- decompose body into conjuncts
- for each conjunct, prove Tendsto
- extract witness
- verify

--------------------------------------------------

Milestone 2 — Single linear bound: ε < δ
------------------------------------------
New capability:
Prove the simplest possible goal:

    (δ : ℝ) (h : 0 < δ) ⊢ ∃ ε : ℝ, 0 < ε ∧ ε < δ

Implementation:
- Use `exact ⟨δ / 2, by linarith, by linarith⟩` as a direct witness.
- This establishes the proof strategy: provide explicit half-bound witness.

--------------------------------------------------

Milestone 3 — Single polynomial bound: ε ^ n < δ
--------------------------------------------------
New capability:
Prove bounds involving polynomial powers:

    ∃ ε : ℝ, 0 < ε ∧ ε ^ 2 < δ
    ∃ ε : ℝ, 0 < ε ∧ ε ^ 3 < δ

Implementation:
- Show `Tendsto (· ^ n) (𝓝 0) (𝓝 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one`
  or `Filter.Tendsto.pow`.
- Extract witness: `ε = min (δ / 2) (1 / 2)`, or use `Filter.Tendsto.eventually`.

Key lemmas:
- `tendsto_nhds_zero_iff` / `Filter.Tendsto.mono_left`
- `Filter.Eventually.exists_pos` (or manual construction)

--------------------------------------------------

Milestone 4 — Scalar multiples: c * ε < δ
-------------------------------------------
New capability:
Handle scalar multiplications:

    ∃ ε : ℝ, 0 < ε ∧ 2 * ε < δ
    ∃ ε : ℝ, 0 < ε ∧ (1/3) * ε < δ

Implementation:
- If `c > 0` is a literal, witness `ε = δ / (2 * c)`.
- Verify with `linarith`.

--------------------------------------------------

Milestone 5 — Conjunctions of two bounds
------------------------------------------
New capability:
Prove goals with two simultaneous bounds:

    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ^ 2 < δ
    ∃ ε : ℝ, 0 < ε ∧ 2 * ε < δ ∧ ε ^ 3 < δ

Implementation:
- Compute individual witnesses `ε₁` and `ε₂` for each bound.
- Take `ε = min ε₁ ε₂`.
- Verify both bounds hold for `ε` using `min_lt_iff` and `linarith`.

--------------------------------------------------

Milestone 6 — Tendsto-based witness extraction
-----------------------------------------------
New capability:
Use the general `Tendsto` API to derive witnesses:

    ∃ ε : ℝ, 0 < ε ∧ Real.sin ε < δ

Implementation:
- For each function `f`, prove `Tendsto f (𝓝 0) (𝓝 0)`.
- Use `Filter.Tendsto.eventually` with the open set `(-δ, δ)` to find `ε₀`.
- Apply `Filter.Eventually.exists` to extract the witness.

Key lemma pattern:
```lean
have ht : Tendsto f (𝓝 0) (𝓝 0) := by continuity / simp / ...
obtain ⟨ε, hε, hfε⟩ := ... ht ...
```

--------------------------------------------------

Milestone 7 — Products and compositions tending to zero
---------------------------------------------------------
New capability:
Handle products and compositions:

    ∃ ε : ℝ, 0 < ε ∧ ε * Real.sin ε < δ
    ∃ ε : ℝ, 0 < ε ∧ (Real.cos ε - 1) < δ

Key lemmas:
- `Filter.Tendsto.mul` : product of two tendsto-zero functions.
- Known limit `Real.tendsto_sin_zero`, `Real.tendsto_cos_nhds`.

Implementation:
- Decompose the expression using `Tendsto.mul`, `Tendsto.add`, etc.
- Each factor must be shown to tend to 0.

--------------------------------------------------

Milestone 8 — N-ary conjunctions
----------------------------------
New capability:
Handle an arbitrary number of conjuncts:

    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε^2 < δ ∧ ε^3 < δ ∧ |ε| < δ ∧ 2*ε < δ

Implementation:
- Generalise Milestone 5: compute all individual witnesses and take their minimum.
- Iterate over the conjunction tree.

--------------------------------------------------

Milestone 9 — Guardrails and failure modes
-------------------------------------------
Add safety checks:

1. **Missing `0 < δ` hypothesis**: Fail with "prove_exists_by_tendsto: need `0 < δ`".
2. **Non-tending functions**: If `Tendsto` proof fails, report which function is problematic.
3. **Non-real types**: Fail clearly for types other than ℝ.
4. **Unsupported conjunct form**: If a conjunct is not of the form `f(ε) < δ`, fail.

--------------------------------------------------

Milestone 10 — Internal refactor for long-term stability
---------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

```
decomposeBody     : Expr → TacticM (List Expr)        -- list of fi(ε)
proveTedstoZero   : Expr → TacticM Unit
computeWitness    : List Expr → ℝ-expr → TacticM Expr
assembleProof     : Expr → List Expr → TacticM Unit
```

Also add trace option `trace.prove_exists_by_tendsto` printing:
- extracted functions
- Tendsto proofs found
- witness computed

--------------------------------------------------

Summary of Milestones
---------------------
| # | Milestone | New Capability |
|---|-----------|----------------|
| 1 | Skeleton | Goal parsing, principled failure |
| 2 | Linear bound | `ε < δ` direct witness |
| 3 | Polynomial powers | `ε^n < δ` |
| 4 | Scalar multiples | `c * ε < δ` |
| 5 | Two conjuncts | `f₁(ε) < δ ∧ f₂(ε) < δ` with min |
| 6 | Tendsto API | `sin ε < δ` via continuity |
| 7 | Products / compositions | `ε * sin ε`, `cos ε - 1` |
| 8 | N-ary conjunctions | Arbitrary number of bounds |
| 9 | Guardrails | Missing hyp, non-real type checks |
| 10 | Refactor | Clean architecture + tracing |
