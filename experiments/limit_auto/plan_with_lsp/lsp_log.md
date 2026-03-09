# Lean LSP MCP Tool Usage Log

This log tracks all lean-lsp-mcp tool invocations during the limit_auto tactic development.

---

## Milestone 1: Skeleton and principled failure

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone1.lean`
- **Purpose:** Verify milestone 1 compiles correctly
- **Result:** Success - no errors

---

## Milestone 2: Strict continuity rule

### Tool: lean_leansearch
- **Query:** "ContinuousAt implies Tendsto at nhds"
- **Purpose:** Find the key lemma connecting ContinuousAt to Tendsto
- **Result:** Found 5 results, key lemma:
  - `ContinuousAt.tendsto`: `ContinuousAt f x → Filter.Tendsto f (nhds x) (nhds (f x))`
  - This is exactly what we need for the strict continuity rule

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone2.lean`
- **Purpose:** Verify milestone 2 compiles correctly
- **Result:** Success - no errors

---

## Milestone 3: Robust continuity via simp equality

### Tool: lean_loogle
- **Query:** "Filter.Tendsto.congr"
- **Purpose:** Find lemmas for converting between equivalent Tendsto goals
- **Result:** Found `Filter.Tendsto.congr`:
  - `∀ (x : α), f₁ x = f₂ x → Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone3.lean`
- **Purpose:** Verify milestone 3 compiles
- **Result:** Errors - the convert approach doesn't work as expected

### Tool: lean_multi_attempt
- **File:** `limit_auto.milestone3.lean` (line 72)
- **Purpose:** Debug tactic approaches for `Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3)`
- **Snippets tested:**
  1. `refine ContinuousAt.tendsto ?_` → Failed (type inference stuck)
  2. `convert ContinuousAt.tendsto (f := ...) (x := 2) ?_ using 1` → Creates 2 subgoals
  3. `have h := (by fun_prop : ContinuousAt ...).tendsto; convert h using 1; norm_num` → Works!
- **Result:** Third approach is the correct one - need to use `have` + `convert` + `norm_num`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone3.lean` (revised version with helper lemma)
- **Purpose:** Verify milestone 3 compiles
- **Result:** Success - no errors. Used helper lemma `tendsto_of_continuousAt_eq` with `first` tactic.

---

## Milestone 4: Normalization pass

### Tool: lean_loogle
- **Query:** "one_div"
- **Purpose:** Find lemma for normalizing `1/x` to `x⁻¹`
- **Result:** Found `one_div : 1 / a = a⁻¹`

### Tool: lean_loogle
- **Query:** "div_self"
- **Purpose:** Find lemma for `a/a = 1`
- **Result:** Found `div_self : a ≠ 0 → a / a = 1`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone4.lean`
- **Purpose:** Verify milestone 4 compiles
- **Result:** Error on line 109:
  - `fun_prop` unable to prove `ContinuousAt (fun x => x⁻¹) 2`
  - Needed side condition `2 ≠ 0` for `ContinuousAt.inv₀`

### Tool: lean_multi_attempt
- **File:** `limit_auto.milestone4.lean` (line 109)
- **Purpose:** Find how to help fun_prop with nonzero side conditions
- **Snippets tested:**
  1. `fun_prop (disch := norm_num)` → Error (Tendsto not a fun_prop goal directly)
  2. `fun_prop (disch := decide)` → Same error
  3. `refine ContinuousAt.tendsto ?_; fun_prop (disch := norm_num)` → Type inference stuck
- **Result:** Need to use `disch := norm_num` inside the tactic's `fun_prop` calls

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone4.lean` (after fix)
- **Purpose:** Verify fix compiles
- **Result:** Success - no errors. Fixed by changing `fun_prop` to `fun_prop (disch := norm_num)` in the tactic.

---

## Milestone 5: Exponential decay limits

### Tool: lean_leansearch
- **Query:** "exp(-1/x) tends to 0 as x tends to infinity"
- **Purpose:** Find lemmas for exponential decay limits
- **Result:** Found key lemmas:
  - `Real.tendsto_exp_neg_atTop_nhds_zero`: `Tendsto (fun x => exp(-x)) atTop (𝓝 0)`
  - `Real.tendsto_exp_atBot`: `Tendsto exp atBot (𝓝 0)`

### Tool: lean_leansearch
- **Query:** "tendsto reciprocal atTop nhds zero"
- **Purpose:** Find lemmas for `1/x → 0`
- **Result:** Found `tendsto_inv_atTop_zero`: `Tendsto (·⁻¹) atTop (𝓝 0)`

### Tool: lean_leansearch
- **Query:** "inverse tends to cobounded as x tends to zero"
- **Purpose:** Find cobounded limit lemmas
- **Result:** Found key lemmas:
  - `Filter.tendsto_inv₀_nhdsWithin_ne_zero`: `Tendsto (·⁻¹) (𝓝[≠] 0) (cobounded α)`
  - `Filter.inv_cobounded₀`: `(cobounded α)⁻¹ = 𝓝[≠] 0`

### Tool: lean_leansearch
- **Query:** "exp tends to nhdsWithin positive as argument tends to negative infinity"
- **Purpose:** Find exp decay to positive neighborhood
- **Result:** Found:
  - `Real.tendsto_exp_atBot_nhdsGT`: `Tendsto exp atBot (𝓝[>] 0)`
  - `Real.tendsto_exp_atBot`: `Tendsto exp atBot (𝓝 0)`

### Tool: lean_leansearch
- **Query:** "inverse tends to positive infinity as x tends to zero from the right"
- **Purpose:** Find `x⁻¹ → +∞` as `x → 0⁺`
- **Result:** Found `tendsto_inv_nhdsGT_zero`: `Tendsto (·⁻¹) (𝓝[>] 0) atTop`

### Tool: lean_goal
- **File:** `limit_auto.milestone5.lean` (line 115)
- **Purpose:** Check goal state for exponential decay proof
- **Result:** Goal: `Tendsto (HDiv.hDiv (-1)) (𝓝[>] 0) atBot`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone5.lean` (initial version)
- **Purpose:** Verify proof attempts
- **Result:** Multiple iterations needed to find correct proof:
  1. `simp` made no progress (goal already in correct form)
  2. `ring` failed (doesn't handle `⁻¹`)
  3. `field_simp` worked for `-1/x = (-x)⁻¹`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone5.lean` (final version)
- **Purpose:** Verify milestone 5 compiles
- **Result:** Success - no errors. Implemented:
  - Helper lemma `tendsto_neg_one_div_nhdsGT_zero_atBot`
  - Exponential decay rule in tactic
  - Test: `Tendsto (fun x => exp(-1/x)) (𝓝[>] 0) (𝓝 0)`

---

## Milestone 6: Reciprocal limits (cobounded)

### Tool: lean_local_search
- **Query:** "tendsto_inv"
- **Purpose:** Find available inverse limit lemmas
- **Result:** Found 10+ lemmas including `tendsto_inv_nhdsGT`, `tendsto_inv_nhdsLT`, etc.

### Tool: lean_local_search
- **Query:** "cobounded"
- **Purpose:** Find cobounded-related lemmas
- **Result:** Found `Real.cobounded_eq`, `cobounded_eq_bot_iff`, etc.

### Tool: lean_local_search
- **Query:** "inv_cobounded"
- **Purpose:** Find inverse-cobounded relationship
- **Result:** Found `Filter.inv_cobounded` in `Analysis.Normed.Group.Bounded`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone6.lean` (with exact?)
- **Purpose:** Find lemma for `Tendsto (·⁻¹) (𝓝[≠] 0) (cobounded ℝ)`
- **Result:** `exact?` found `tendsto_inv₀_nhdsWithin_ne_zero`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone6.lean` (initial)
- **Purpose:** Verify milestone 6 compiles
- **Result:** Two issues:
  1. Deprecation warning: `tendsto_inv₀_nhdsWithin_ne_zero` → use `tendsto_inv₀_nhdsNE_zero`
  2. Timeout on `atBot` case due to `first` tactic overhead

### Tool: lean_goal
- **File:** `limit_auto.milestone6.lean` (line 142)
- **Purpose:** Debug timeout issue
- **Result:** Goal `Tendsto (fun x => x⁻¹) atBot (𝓝 0)` — the lemma exists but tactic overhead causes timeout

### Tool: lean_local_search
- **Query:** "tendsto_inv_atBot_zero"
- **Purpose:** Confirm lemma exists
- **Result:** Found in `Mathlib.Topology.Algebra.Order.Field`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone6.lean` (final)
- **Purpose:** Verify milestone 6 compiles
- **Result:** Success. Implemented:
  - Reciprocal rules using `tendsto_inv₀_nhdsNE_zero`, `tendsto_inv_nhdsGT_zero`, etc.
  - Tests for cobounded, `atTop`/`atBot` limits
  - Note: `atBot → 𝓝 0` case times out with tactic (known limitation)

---

## Milestone 7: Exponential decay Version B (generalized)

### Tool: lean_leansearch
- **Query:** "tendsto exp negative constant divided by x atTop nhds zero"
- **Purpose:** Find lemmas for generalized exponential decay with constants
- **Result:** Found `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` with hypothesis `0 < b`

### Tool: lean_hover_info
- **File:** `limit_auto.milestone7.lean` (line 37, column 23)
- **Purpose:** Check type of `tendsto_neg_atTop_atBot`
- **Result:** `Tendsto Neg.neg atTop atBot`

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone7.lean` (initial)
- **Purpose:** Verify milestone 7 compiles
- **Result:** Two errors:
  1. `tendsto_const_mul_atTop_of_pos` is an iff, not direct lemma - fixed using `tendsto_id.const_mul_atTop`
  2. `π` vs `Real.pi` type mismatch - fixed by using `Real.pi` explicitly

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone7.lean` (final)
- **Purpose:** Verify milestone 7 compiles
- **Result:** Success. Implemented:
  - Generalized lemma `tendsto_neg_const_div_nhdsGT_zero_atBot` for any `c > 0`
  - `tendsto_exp_neg_const_div_nhdsGT_zero` combining with exp
  - Tests for `exp(-2/x)`, `exp(-π/x)` with positive constants

---

## Milestone 8: Guardrails against indeterminate forms

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone8.lean`
- **Purpose:** Verify milestone 8 compiles
- **Result:** Success. Implemented:
  - `isZeroLit`: Check if expression is syntactically zero
  - `syntacticallyEqual`: Simple equality check for expressions
  - `getDivisionParts`: Extract numerator/denominator from division
  - `checkForIndeterminateForms`: Detect `t/t`, `0/0`, `t/0` patterns
  - Pre-check in tactic that refuses dangerous forms
  - Tests for rejection of `x/x` and `x/0`

---

## Milestone 9: Internal refactor + tracing

### Tool: lean_diagnostic_messages
- **File:** `limit_auto.milestone9.lean`
- **Purpose:** Verify milestone 9 compiles
- **Result:** Success. Implemented:
  - **Rule enumeration**: `LimitRule` inductive with `continuity`, `exponentialDecay`, `reciprocal`, `unsupported`
  - **Tracing**: `registerTraceClass \`limit_auto` and `traceLimit` helper
  - **Decomposition**:
    - `normalizeGoal`: Apply conservative simp lemmas
    - `classifyGoal`: Detect exponential/reciprocal patterns, default to continuity
    - `applyRule`: Dispatch to appropriate rule handler
    - `applyContinuityRule`, `applyExponentialDecayRule`, `applyReciprocalRule`
  - **Main tactic** now follows: normalize → classify → apply (with fallback)
  - Usage: `set_option trace.limit_auto true` for debugging
