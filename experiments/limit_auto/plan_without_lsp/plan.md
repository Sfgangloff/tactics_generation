limit_auto — Incremental Refinement Plan

Philosophy
----------
We implement a single tactic `limit_auto` that evolves through milestones. Each milestone strictly refines the previous one: it either proves more goals, improves robustness, or increases safety — never weakening earlier behavior.

We enforce:
1. Monotonic test suite (never delete tests unless intentionally changing behavior).
2. Deterministic rule ordering.
3. Conservative normalization.
4. One canonical lemma per pattern whenever possible.

--------------------------------------------------

Milestone 1 — Skeleton and principled failure
--------------------------------------------
Behavior:
- If the goal is not `Tendsto _ _ _`, fail with a clear message.
- If it is a `Tendsto` goal but unsupported, fail with “unsupported shape”.

Architecture (future‑proof):
- normalize goal
- try rules in fixed order
- fail

This dispatcher remains unchanged throughout the project.

--------------------------------------------------

Milestone 2 — Strict continuity rule
------------------------------------
New capability:
Prove goals of the exact form:

    Tendsto f (𝓝 a) (𝓝 (f a))

whenever `by continuity` produces `ContinuousAt f a`.

Important constraints:
- Do NOT attempt simp rewriting yet.
- Require the target literally to be `𝓝 (f a)`.

Why this comes first:
- deterministic
- mathematically clean
- creates a reliable baseline rule

--------------------------------------------------

Milestone 3 — Robust continuity via simp equality
-------------------------------------------------
Refinement of Milestone 2.

Now allow targets:

    Tendsto f (𝓝 a) (𝓝 b)

provided `simp` can prove:

    b = f a

Implementation idea:
1. Attempt `have : b = f a := by simp`
2. Rewrite the target
3. Apply `ContinuousAt.tendsto`

Milestone 2 becomes a special case of this one.

--------------------------------------------------

Milestone 4 — Normalization pass
--------------------------------
Before dispatching rules, run a lightweight normalization step.

Goals:
- improve pattern matching
- avoid duplicating rules for syntactic variants
- remain predictable (no aggressive simp)

Examples of good rewrites:
- `1 / x` → `x⁻¹`
- trivial arithmetic (`x + 0`, `(-1) * t`, etc.)
- definitional equalities

Avoid:
- heavy algebra
- rewriting that may expand expressions
- unbounded simp calls

This milestone strengthens ALL later rules.

--------------------------------------------------

Milestone 5 — Reciprocal / cobounded rule
----------------------------------------
Add a new dispatch branch handling any `[NormedField 𝕜]`:

    Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[≠] 0) cobounded
    Tendsto (fun x : 𝕜 => x⁻¹) cobounded (𝓝[≠] 0)

Because of Milestone 4, both `1/x` and `x⁻¹` match.

Implementation principles:
- locate the exact Mathlib lemmas once
- wrap them directly
- avoid search

Effect:
Previously these goals failed; now they succeed.

--------------------------------------------------

Milestone 6 — Exponential decay (Version A)
------------------------------------------
Start with ONE canonical pattern only.

Example:

    Tendsto (fun x : ℝ => Real.exp (-1/x)) atTop (𝓝 0)

Why restrict initially:
Exponential lemmas are sensitive to:
- ℝ vs ℂ
- approach filters (atTop vs 𝓝[>] 0)
- syntactic shape

Pick one lemma and match it exactly.

Do not generalize yet.

--------------------------------------------------

Milestone 7 — Exponential decay (Version B)
------------------------------------------
Refinement of Milestone 6.

Generalize to:

    exp (-(c/x))   with hypothesis   0 < c

Accept syntactic variants after normalization:
- `-(c * (1/x))`
- `(-c)/x`
- etc.

Possible extensions:
- support multiple filters if useful
- allow constants from hypotheses

This milestone is about a better classifier — not broader search.

--------------------------------------------------

Milestone 8 — Guardrails against indeterminate forms
---------------------------------------------------
Add a pre-check that refuses dangerous syntactic patterns such as:

- `(t)/(t)`
- `(t - a)/(t - a)`
- `0/0`
- `t/0`

This is intentionally syntactic — perfection is unnecessary.

Goal:
Increase trust in the tactic.

It is better to fail than to “solve” nonsense.

--------------------------------------------------

Milestone 9 — Internal refactor for long-term stability
------------------------------------------------------
No new mathematical power — only structural improvement.

Recommended decomposition:

normalize   : Expr → TacticM Expr
classify    : (f, F, G) → Option Rule
applyRule   : Rule → TacticM Unit

Also strongly recommended:
Add a trace option (e.g. `trace.limit_auto`) printing:
- detected rule
- matched subexpressions
- lemma used

This makes future extensions safe.

--------------------------------------------------

Ordering Discipline
-------------------
To guarantee refinement:

1. Keep all earlier tests.
2. Maintain a fixed rule priority.
3. Insert new rules deliberately.
4. Ensure normalization is conservative.

A good default priority is:

    specialized theorems
    → reciprocal
    → exponential
    → continuity
    → failure

(But choose once and keep it stable.)

--------------------------------------------------

Guiding Principle for Future Growth
----------------------------------
When encountering a new limit you want automated:

DO NOT immediately make the tactic smarter.

Instead:
1. Prove a clean standalone lemma.
2. Add a rule that applies exactly that lemma.

This keeps `limit_auto` mathematical rather than heuristic,
predictable rather than magical,
and therefore usable in serious developments.
