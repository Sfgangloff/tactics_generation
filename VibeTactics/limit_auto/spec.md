> **User Request:** A tactic that proves limit statements (tendsto goals) by analyzing the mathematical structure of the limit expression. The tactic should handle simple continuous cases using continuity arguments (like Continuous.tendsto' (by continuity) _ _ (by simp)), more complex cases involving exponential decay (e.g., exp(-1/x) tends to 𝓝[>] 0 as x tends to atTop), and reciprocal relationships in normed fields (e.g., 1/x tends to cobounded as x tends to 𝓝[≠] 0 and vice versa). The tactic should work for any normed field, not just reals, and should avoid indeterminate forms like 0/0. It should automatically select the appropriate approach based on the structure of the limit expression.

---

# Tactic Specification: limit_auto

## Analysis

## Tactic Analysis: limit_auto

### 1. Tactic Name
`limit_auto`

### 2. Scope Analysis

**Most general interpretation**: A tactic that could prove any limit statement by automatically analyzing the mathematical structure and selecting from all possible limit theorems and techniques in analysis.

**Lean constraints**: 
- Expression pattern matching is limited to syntactic structure
- Cannot perform symbolic computation or algebraic manipulation beyond basic simplification
- Must rely on existing Mathlib theorems rather than mathematical reasoning
- Decidability requirements for termination
- Limited ability to handle arbitrary mathematical transformations

**Implementation complexity**: A fully general limit solver would require:
- Comprehensive expression analysis and classification
- Integration with computer algebra systems
- Heuristic search through vast theorem spaces
- Complex case analysis for indeterminate forms

**Chosen scope**: I will target a syntactic pattern-matching approach that handles three specific classes of limit expressions:

1. **Continuity-based limits**: `f x → L` where `f` is continuous at the limit point
2. **Exponential decay limits**: Expressions involving `exp(-c/x)` as `x → ∞` for positive `c`
3. **Reciprocal limits**: `1/x` relationships between `𝓝[≠] 0` and `cobounded` filters

This scope is implementable through syntactic analysis while covering the user's main examples, and avoids the undecidable problem of general limit evaluation.

### 3. Mathematical Specification

**Class of formulas**: Goals of the form `Tendsto f F G` where:
- `f : α → β` for appropriate topological spaces `α`, `β`
- `F : Filter α` and `G : Filter β`
- The expression `f` matches one of these syntactic patterns:
  
  ```
  Class₁ = {f | f is syntactically continuous and ∃ continuous lemma in context}
  Class₂ = {exp ∘ (λ x, -c / x) | c > 0} ∪ {λ x, exp(-c / x) | c > 0}  
  Class₃ = {λ x, x⁻¹ | domain is normed field} ∪ {λ x, 1/x | domain is normed field}
  ```

**Logical fragment**: First-order logic with arithmetic over normed fields and topological predicates.

**Provability conditions**: A formula `Tendsto f F G` is provable by this tactic iff:
- `f ∈ Class₁` and there exists a continuity proof in the local context
- `f ∈ Class₂` and `F = atTop` and `G = 𝓝[>] 0`
- `f ∈ Class₃` and `(F = 𝓝[≠] 0 ∧ G = cobounded) ∨ (F = cobounded ∧ G = 𝓝[≠] 0)`

### 4. Purpose
A tactic that automatically proves limit statements by pattern-matching on limit expressions and applying appropriate continuity, exponential decay, or reciprocal limit theorems.

### 5. Input Types
- **Goals**: `Tendsto f F G` where `f : α → β`, `F : Filter α`, `G : Filter β`
- **Context**: May use continuous function instances and normed field structures

### 6. Algorithm

1. **Goal Analysis**: Parse the goal to extract `f`, `F`, and `G` from `Tendsto f F G`

2. **Pattern Classification**: 
   - Check if `f` matches continuity patterns (compositions of known continuous functions)
   - Check if `f` matches exponential decay patterns `exp(-c/x)` 
   - Check if `f` matches reciprocal patterns `x⁻¹` or `1/x`

3. **Proof Construction**:
   - **Continuity case**: Apply `Continuous.tendsto'` with `by continuity` for the continuity proof and `by simp` for the evaluation
   - **Exponential decay case**: Apply specialized exponential limit theorems from Mathlib
   - **Reciprocal case**: Apply `tendsto_inv_cobounded_nhds` or `tendsto_inv_nhds_cobounded`

4. **Fallback**: If no patterns match, fail with informative error message

### 7. Success Criteria

**Success**: 
- Goal matches one of the three syntactic patterns
- Required mathematical conditions are satisfied (continuity proofs available, positive constants, correct filter pairs)
- Mathlib contains the necessary limit theorems

**Failure**:
- Goal is not a `Tendsto` statement
- Expression doesn't match any supported patterns
- Indeterminate forms detected (e.g., `0/0` patterns)
- Required auxiliary proofs cannot be constructed

### 8. Edge Cases

- **Indeterminate forms**: Detect and reject patterns like `(x-a)/(x-a)` that could lead to `0/0`
- **Complex expressions**: Handle only direct pattern matches, not algebraically equivalent forms
- **Filter mismatches**: Ensure filter pairs match expected patterns for each limit type
- **Type inference**: Handle cases where normed field structure isn't automatically inferred
- **Constant sign**: For exponential decay, verify constants are positive when possible

### 9. Dependencies

```lean
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv  
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
```

The tactic would likely need additional specific limit theorems from Mathlib's analysis library, particularly for exponential decay patterns which may require development of new auxiliary lemmas.

## Test Generation Algorithm

# Test Case Generation Algorithm for `limit_auto` Tactic

## 1. Input Parameters

```lean
structure LimitTestConfig where
  max_function_depth : Nat := 3        -- Maximum composition depth for functions
  num_variables : Nat := 5              -- Pool of variable names to use
  include_continuity : Bool := true     -- Generate continuity-based limits
  include_exponential : Bool := true    -- Generate exponential decay limits  
  include_reciprocal : Bool := true     -- Generate reciprocal limits
  constant_range : List ℝ := [1, 2, π, ℯ]  -- Pool of positive constants
  variable_pool : List String := ["x", "y", "z", "t", "u"]
```

## 2. Core Algorithm

### Phase 1: Formula Structure Enumeration

**Step 1: Generate Base Function Patterns**

For each enabled pattern class, enumerate syntactic structures:

```lean
-- Class 1: Continuity-based functions
def generate_continuous_patterns (depth : Nat) : List FunctionPattern :=
  match depth with
  | 0 => [id, const c]  -- Base cases
  | n+1 => 
    let prev := generate_continuous_patterns n
    prev ++ 
    [f + g | f, g ∈ prev] ++
    [f * g | f, g ∈ prev] ++
    [f ∘ g | f, g ∈ prev] ++
    [sin f, cos f, exp f | f ∈ prev]

-- Class 2: Exponential decay patterns  
def generate_exponential_patterns (constants : List ℝ) : List FunctionPattern :=
  [λ x, exp(-c/x) | c ∈ constants] ++
  [λ x, exp(-c*x) | c ∈ constants] ++  -- atTop variant
  [λ x, c * exp(-1/x) | c ∈ constants]

-- Class 3: Reciprocal patterns
def generate_reciprocal_patterns : List FunctionPattern :=
  [λ x, x⁻¹, λ x, 1/x, λ x, x⁻², λ x, 1/(x²)]
```

**Step 2: Generate Filter Pair Combinations**

```lean
def generate_filter_pairs (pattern_class : PatternClass) : List (Filter, Filter) :=
  match pattern_class with
  | Continuity => 
    [(𝓝 a, 𝓝 (f a)) | a ∈ evaluation_points] ++
    [(atTop, atTop), (atBot, atBot), (𝓝 ∞, 𝓝 L)]
  | Exponential =>
    [(atTop, 𝓝 0), (𝓝[>] 0, 𝓝 1), (atBot, 𝓝 0)]
  | Reciprocal =>
    [(𝓝[≠] 0, cobounded), (cobounded, 𝓝[≠] 0), (𝓝[>] 0, atTop)]
```

**Step 3: Cross-Product Generation**

```lean
def generate_raw_formulas (config : LimitTestConfig) : List LimitFormula :=
  let patterns := []
  if config.include_continuity then 
    patterns := patterns ++ generate_continuous_patterns config.max_function_depth
  if config.include_exponential then
    patterns := patterns ++ generate_exponential_patterns config.constant_range  
  if config.include_reciprocal then
    patterns := patterns ++ generate_reciprocal_patterns
  
  [Tendsto f F G | f ∈ patterns, (F,G) ∈ generate_filter_pairs (classify f)]
```

### Phase 2: Provability Filtering

**Step 4: Syntactic Provability Check**

```lean
def is_provable_by_limit_auto (formula : LimitFormula) : Bool :=
  match formula with
  | Tendsto f F G =>
    match classify_pattern f with
    | Continuity => 
      check_continuity_conditions f ∧ 
      check_filter_compatibility F G (evaluate_limit f F)
    | Exponential => 
      check_exponential_form f ∧ 
      check_exponential_filters F G ∧
      check_positive_constants f
    | Reciprocal =>
      check_reciprocal_form f ∧ 
      check_reciprocal_filters F G
    | Unknown => false

-- Specific checks for each pattern class
def check_continuity_conditions (f : FunctionPattern) : Bool :=
  is_composition_of_continuous_functions f ∧
  ¬has_indeterminate_forms f

def check_exponential_filters (F G : Filter) : Bool :=
  (F = atTop ∨ F = atBot) ∧ (G = 𝓝 0 ∨ G = 𝓝[>] 0)

def check_reciprocal_filters (F G : Filter) : Bool :=
  (F = 𝓝[≠] 0 ∧ G = cobounded) ∨ 
  (F = cobounded ∧ G = 𝓝[≠] 0) ∨
  (F = 𝓝[>] 0 ∧ G = atTop)
```

**Step 5: Mathematical Consistency Check**

```lean
def verify_mathematical_correctness (formula : LimitFormula) : Bool :=
  match formula with
  | Tendsto f F G =>
    -- Check that the limit actually exists and equals the target
    let expected_limit := compute_expected_limit f F
    match expected_limit with
    | Some L => filter_matches G L
    | None => false  -- Limit doesn't exist

def compute_expected_limit (f : FunctionPattern) (F : Filter) : Option Value :=
  match (f, F) with
  | (λ x, exp(-c/x), atTop) => Some 0  -- where c > 0
  | (λ x, x⁻¹, 𝓝[≠] 0) => None  -- Goes to ±∞, so cobounded
  | (continuous_f, 𝓝 a) => Some (f a)  -- By continuity
  | _ => compute_symbolically f F  -- Fallback symbolic computation
```

### Phase 3: Test Case Refinement

**Step 6: Add Contextual Variants**

```lean
def add_contextual_variants (base_formulas : List LimitFormula) : List TestCase :=
  base_formulas.flatMap fun formula =>
    -- Add different context assumptions
    [TestCase.simple formula] ++
    [TestCase.with_continuity_hyp formula] ++  -- Add explicit continuity
    [TestCase.with_field_instance formula] ++  -- Add normed field instance
    [TestCase.with_simp_lemmas formula]        -- Add relevant simp lemmas
```

**Step 7: Difficulty Stratification**

```lean
def stratify_by_difficulty (test_cases : List TestCase) : List (Difficulty × TestCase) :=
  test_cases.map fun tc =>
    let difficulty := 
      if is_direct_pattern_match tc then Difficulty.Easy
      else if requires_type_inference tc then Difficulty.Medium  
      else if has_complex_composition tc then Difficulty.Hard
      else Difficulty.Medium
    (difficulty, tc)
```

## 3. Provability Criteria

A generated theorem `Tendsto f F G` is kept if and only if:

1. **Syntactic Match**: `f` matches exactly one of the three pattern classes
2. **Filter Compatibility**: The filter pair `(F,G)` is valid for that pattern class:
   - Continuity: `F = 𝓝 a, G = 𝓝 (f a)` or asymptotic pairs
   - Exponential: `F ∈ {atTop, atBot}, G ∈ {𝓝 0, 𝓝[>] 0}`  
   - Reciprocal: `(F,G) ∈ {(𝓝[≠] 0, cobounded), (cobounded, 𝓝[≠] 0)}`
3. **Mathematical Validity**: The limit actually exists and has the expected value
4. **No Edge Cases**: Avoids indeterminate forms, negative constants in exponentials, etc.
5. **Provability in Mathlib**: Required auxiliary lemmas (continuity, positivity) are available

## 4. Example Outputs

The algorithm would generate test cases like:

### Easy Cases (Direct Pattern Matching)
```lean
-- Continuity-based
example : Tendsto (fun x : ℝ => x + 1) (𝓝 2) (𝓝 3) := by limit_auto

-- Exponential decay  
example : Tendsto (fun x : ℝ => exp (-1/x)) atTop (𝓝 0) := by limit_auto

-- Reciprocal
example : Tendsto (fun x : ℝ => x⁻¹) (𝓝[≠] 0) cobounded := by limit_auto
```

### Medium Cases (Requiring Type Inference)
```lean
-- Composition of continuous functions
example : Tendsto (fun x : ℝ => sin (x^2 + 1)) (𝓝 0) (𝓝 (sin 1)) := by limit_auto

-- Scaled exponential
example : Tendsto (fun x : ℝ => 2 * exp (-π/x)) atTop (𝓝 0) := by limit_auto

-- Reciprocal with power
example : Tendsto (fun x : ℝ => 1/(x^2)) (𝓝[≠] 0) cobounded := by limit_auto
```

### Hard Cases (Complex Compositions)
```lean
-- Nested continuous functions
example : Tendsto (fun x : ℝ => exp (sin (cos x))) (𝓝 π) (𝓝 (exp (sin (cos π)))) := by limit_auto

-- Multiple exponential terms
example : Tendsto (fun x : ℝ => exp (-2/x) + exp (-3/x)) atTop (𝓝 0) := by limit_auto

-- Continuous function approaching reciprocal singularity  
example {f : ℝ → ℝ} (hf : Continuous f) : 
  Tendsto (fun x => f (1/x)) cobounded (𝓝 (f 0)) := by limit_auto
```

### Edge Case Tests (Should Fail)
```lean
-- Indeterminate form - should fail
example : Tendsto (fun x : ℝ => (x-1)/(x-1)) (𝓝 1) (𝓝 1) := by limit_auto

-- Wrong filter pair - should fail  
example : Tendsto (fun x : ℝ => exp (-1/x)) (𝓝 0) (𝓝 0) := by limit_auto

-- Non-matching pattern - should fail
example : Tendsto (fun x : ℝ => x/(x+1)) atTop (𝓝 1) := by limit_auto
```

This algorithm systematically generates a comprehensive test suite covering the tactic's intended functionality while ensuring all generated theorems are actually provable by the pattern-matching approach.
