> **User Request:** Prove existential statements of the form `∃ ε > 0, P(ε) < δ ∧ Q(ε) < δ` where `δ > 0` is given, by establishing that the functions in the conditions tend to 0 as ε approaches 0. The tactic works by: 1) Proving `Tendsto (fun ε ↦ P(ε)) (nhds 0) (nhds 0)` for each function P(ε), Q(ε), etc. in the conditions, 2) Using these limit facts to find a witness ε₀ > 0 such that all inequalities P(ε₀) < δ, Q(ε₀) < δ, etc. are satisfied. This handles cases like proving `∃ ε > 0, ε^2 + 5*ε + sin ε < δ ∧ 3*ε < δ` from the hypothesis `0 < δ`.

---

# Tactic Specification: prove_exists_by_tendsto

## Analysis

# Tactic Analysis: `prove_exists_by_tendsto`

## 1. Tactic Name
`prove_exists_by_tendsto`

## 2. Scope Analysis

**Most general interpretation**: The broadest interpretation would handle arbitrary existential statements of the form `∃ x, P(x)` where the witness can be found by proving that certain functions tend to specific limits, with arbitrary quantifier structure and logical connectives.

**Lean constraints**: 
- Expression matching in Lean 4 requires concrete syntactic patterns
- The `Tendsto` API in Mathlib provides good support for limit reasoning
- Metaprogramming can effectively decompose conjunctions and inequalities
- Finding witnesses requires either constructive proofs or classical reasoning with computable bounds

**Implementation complexity**: 
- Parsing arbitrary logical formulas is complex
- Automated limit proving for general functions is undecidable
- Managing multiple inequalities and their interactions adds significant complexity
- The tactic should focus on common patterns rather than full generality

**Chosen scope**: I target existential statements of the form `∃ ε > 0, ⋀ᵢ fᵢ(ε) < δ` where:
- The domain is `ℝ` with `δ > 0` given in the context
- Each `fᵢ` is a function that can be proven to tend to 0 at 0
- The conjunction contains only strict inequalities of this form
- This balances practical utility (covers the user's examples) with implementability (concrete syntactic patterns, well-understood limit theory)

## 3. Mathematical Specification

**Class of formulas**: 
```
Goals := {∃ ε > 0, ⋀ᵢ₌₁ⁿ fᵢ(ε) < δ | n ∈ ℕ₊, δ > 0, ∀i. fᵢ: ℝ → ℝ ∧ Tendsto fᵢ (𝓝 0) (𝓝 0)}
```

**Logical fragment**: First-order logic with real arithmetic, specifically existential statements with conjunctive inequality constraints.

**Provability conditions**: A goal `∃ ε > 0, ⋀ᵢ fᵢ(ε) < δ` is provable if and only if:
1. `0 < δ` (available in context)
2. For each `i`, `Tendsto (fun ε ↦ fᵢ(ε)) (𝓝 0) (𝓝 0)` is provable
3. Each `fᵢ` is continuous at 0 (usually follows from tendsto condition)

The mathematical foundation relies on the fact that if `f → 0` as `x → 0`, then for any `δ > 0`, there exists a neighborhood of 0 where `|f(x)| < δ`.

## 4. Purpose
Proves existential statements about finding small positive values where multiple functions are bounded by a given threshold, using limit analysis.

## 5. Input Types
- **Goal**: `∃ ε : ℝ, 0 < ε ∧ ⋀ᵢ fᵢ(ε) < δ` where `δ : ℝ` and `0 < δ` is available
- **Context**: Must contain hypothesis `0 < δ` for some `δ`
- **Functions**: `fᵢ : ℝ → ℝ` appearing in the inequalities

## 6. Algorithm

1. **Goal decomposition**: Parse the goal to extract:
   - The existential variable `ε`
   - The positivity condition `0 < ε`  
   - The conjunction of inequalities `fᵢ(ε) < δ`
   - The threshold value `δ`

2. **Context analysis**: Locate hypothesis `0 < δ` in the local context

3. **Function extraction**: For each inequality `fᵢ(ε) < δ`, extract the function `fᵢ`

4. **Limit proving**: For each function `fᵢ`, attempt to prove `Tendsto (fun ε ↦ fᵢ(ε)) (𝓝 0) (𝓝 0)` using:
   - Simp with continuity/limit lemmas
   - The `continuity` tactic for simple cases
   - Specialized limit tactics if available

5. **Witness construction**: Use the tendsto proofs with `exists_pos_of_tendsto` or similar lemmas to find `ε₀ > 0` such that all inequalities hold

6. **Proof assembly**: Combine the witness with the inequality proofs to construct the final existential proof

## 7. Success Criteria

**Success conditions**:
- Goal matches the expected existential pattern exactly
- Context contains `0 < δ` hypothesis  
- All functions `fᵢ` can be proven to tend to 0 at 0
- No parsing ambiguities in the goal structure

**Failure conditions**:
- Goal is not an existential of the required form
- Missing or unprovable `0 < δ` hypothesis
- Any function `fᵢ` fails the tendsto proof
- Syntactic complexity exceeds pattern matching capabilities

## 8. Edge Cases

- **Empty conjunction**: `∃ ε > 0, True` - should succeed trivially with any small positive ε
- **Single inequality**: `∃ ε > 0, f(ε) < δ` - reduced case of the general pattern
- **Non-continuous functions**: Functions where tendsto fails - should report clear error
- **Zero threshold**: `δ = 0` case - should fail gracefully with appropriate error message
- **Complex function expressions**: Nested operations that make limit proving difficult - may need user assistance

## 9. Dependencies

```lean
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousFunction.Basic  
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Mean
import Mathlib.Tactic.Continuity
import Mathlib.Order.Filter.Basic
```

Key lemmas likely needed:
- `Filter.Tendsto` and related API
- `exists_pos_of_tendsto` (or similar witness extraction lemmas)
- Continuity and limit properties of basic functions (`pow`, `sin`, `cos`, etc.)
- Arithmetic operations preserving limits

## Test Generation Algorithm

# Test Case Generation Algorithm for `prove_exists_by_tendsto`

## 1. Input Parameters

```lean
structure TestGenParams where
  max_conjuncts : Nat := 5        -- Maximum number of inequalities in conjunction
  min_conjuncts : Nat := 1        -- Minimum number of inequalities
  max_expr_depth : Nat := 3       -- Maximum nesting depth of function expressions
  include_trigonometric : Bool := true  -- Include sin, cos functions
  include_polynomial : Bool := true     -- Include polynomial functions
  include_exponential : Bool := false   -- Include exp functions (harder to prove)
  variable_names : List String := ["ε", "δ", "x", "h"]  -- Available variable names
  threshold_names : List String := ["δ", "M", "bound"]  -- Names for threshold constants
```

## 2. Core Algorithm

### Step 1: Function Expression Generation

Generate functions `f : ℝ → ℝ` that tend to 0 at 0:

```lean
inductive TendsToZeroExpr where
  | var : String → TendsToZeroExpr                    -- ε
  | pow : TendsToZeroExpr → Nat → TendsToZeroExpr     -- ε^n (n ≥ 1)
  | mul : TendsToZeroExpr → TendsToZeroExpr → TendsToZeroExpr  -- f * g
  | sin : TendsToZeroExpr → TendsToZeroExpr           -- sin(f)
  | cos_minus_one : TendsToZeroExpr → TendsToZeroExpr -- cos(f) - 1
  | abs : TendsToZeroExpr → TendsToZeroExpr           -- |f|
  | scalar_mul : ℚ → TendsToZeroExpr → TendsToZeroExpr -- c * f (c ≠ 0)
```

**Generation procedure**:
1. Start with base cases: `var "ε"`
2. Recursively apply constructors up to `max_expr_depth`
3. Ensure all generated expressions have the property `Tendsto f (𝓝 0) (𝓝 0)`

### Step 2: Provability-Preserving Constructors

Define expression builders that preserve the tendsto-to-zero property:

```lean
def generate_tendsto_zero_expr (depth : Nat) (params : TestGenParams) : List TendsToZeroExpr :=
  if depth = 0 then
    [TendsToZeroExpr.var "ε"]  -- Base case
  else
    let smaller := generate_tendsto_zero_expr (depth - 1) params
    let mut result := smaller
    
    -- Add polynomial powers
    if params.include_polynomial then
      for expr in smaller do
        for n in [2, 3, 4] do  -- Higher powers tend to zero faster
          result := (TendsToZeroExpr.pow expr n) :: result
    
    -- Add products (both factors must tend to zero)
    for f in smaller do
      for g in smaller do
        result := (TendsToZeroExpr.mul f g) :: result
    
    -- Add trigonometric functions
    if params.include_trigonometric then
      for expr in smaller do
        result := (TendsToZeroExpr.sin expr) :: result
        result := (TendsToZeroExpr.cos_minus_one expr) :: result
    
    -- Add scalar multiples
    for c in [1/2, 2, 3, 1/3] do
      for expr in smaller do
        result := (TendsToZeroExpr.scalar_mul c expr) :: result
    
    result
```

### Step 3: Context Generation

Generate valid mathematical contexts:

```lean
structure TestContext where
  threshold_var : String        -- δ, M, etc.
  threshold_pos : String        -- hypothesis name for "0 < δ"
  additional_hyps : List String -- other relevant hypotheses

def generate_contexts (params : TestGenParams) : List TestContext :=
  params.threshold_names.map fun name =>
    { threshold_var := name
      threshold_pos := s!"h_{name}_pos"  
      additional_hyps := [] }
```

### Step 4: Goal Structure Generation

Generate the existential goal patterns:

```lean
structure ExistentialGoal where
  exists_var : String                    -- ε
  positivity : String                   -- "0 < ε"
  inequalities : List (TendsToZeroExpr × String)  -- (f(ε), δ) for "f(ε) < δ"

def generate_goal_structures (params : TestGenParams) : List ExistentialGoal :=
  let expr_lists := (List.range (params.max_conjuncts - params.min_conjuncts + 1)).map 
    fun i => params.min_conjuncts + i
  
  let expressions := generate_tendsto_zero_expr params.max_expr_depth params
  
  expr_lists.bind fun n =>
    -- Generate all combinations of n expressions with thresholds
    let combinations := choose_n expressions n
    combinations.map fun exprs =>
      { exists_var := "ε"
        positivity := "0 < ε"
        inequalities := exprs.map fun expr => (expr, "δ") }
```

### Step 5: Provability Verification

Ensure generated theorems are provable:

```lean
def is_provable_combination (exprs : List TendsToZeroExpr) : Bool :=
  -- Check that all expressions genuinely tend to zero
  exprs.all fun expr =>
    match expr with
    | TendsToZeroExpr.var _ => true  -- ε → 0 as ε → 0
    | TendsToZeroExpr.pow f n => n ≥ 1 && is_provable_combination [f]  -- Higher powers OK
    | TendsToZeroExpr.mul f g => is_provable_combination [f] && is_provable_combination [g]
    | TendsToZeroExpr.sin f => is_provable_combination [f]  -- sin continuous at 0
    | TendsToZeroExpr.cos_minus_one f => is_provable_combination [f]  -- cos(x)-1 ~ -x²/2
    | TendsToZeroExpr.abs f => is_provable_combination [f]  -- |f| tends to 0 iff f does
    | TendsToZeroExpr.scalar_mul c f => c ≠ 0 && is_provable_combination [f]
```

### Step 6: Lean Code Generation

Convert internal representations to Lean theorem statements:

```lean
def expr_to_lean_string (expr : TendsToZeroExpr) : String :=
  match expr with
  | TendsToZeroExpr.var v => v
  | TendsToZeroExpr.pow f n => s!"({expr_to_lean_string f})^{n}"
  | TendsToZeroExpr.mul f g => s!"({expr_to_lean_string f}) * ({expr_to_lean_string g})"
  | TendsToZeroExpr.sin f => s!"sin({expr_to_lean_string f})"
  | TendsToZeroExpr.cos_minus_one f => s!"(cos({expr_to_lean_string f}) - 1)"
  | TendsToZeroExpr.abs f => s!"|{expr_to_lean_string f}|"
  | TendsToZeroExpr.scalar_mul c f => s!"{c} * ({expr_to_lean_string f})"

def goal_to_lean_theorem (goal : ExistentialGoal) (ctx : TestContext) (name : String) : String :=
  let inequalities_str := goal.inequalities.map 
    fun (expr, threshold) => s!"{expr_to_lean_string expr} < {threshold}"
  let conjunction := inequalities_str.foldl (fun acc ineq => 
    if acc.isEmpty then ineq else s!"{acc} ∧ {ineq}") ""
  
  s!"theorem {name} ({ctx.threshold_var} : ℝ) (h : 0 < {ctx.threshold_var}) : 
     ∃ {goal.exists_var} : ℝ, {goal.positivity} ∧ {conjunction} := by
     prove_exists_by_tendsto"
```

## 3. Complete Generation Pipeline

```lean
def generate_test_cases (params : TestGenParams) : List String :=
  let contexts := generate_contexts params
  let goals := generate_goal_structures params
  let mut test_cases := []
  let mut counter := 1
  
  for ctx in contexts do
    for goal in goals do
      -- Only include provable combinations
      if is_provable_combination (goal.inequalities.map Prod.fst) then
        let theorem_name := s!"test_prove_exists_by_tendsto_{counter}"
        let lean_code := goal_to_lean_theorem goal ctx theorem_name
        test_cases := lean_code :: test_cases
        counter := counter + 1
  
  test_cases
```

## 4. Example Generated Theorems

The algorithm would generate theorems like these:

### Simple Cases
```lean
theorem test_prove_exists_by_tendsto_1 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ ε < δ := by
  prove_exists_by_tendsto

theorem test_prove_exists_by_tendsto_2 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ ε^2 < δ := by
  prove_exists_by_tendsto
```

### Multiple Conjuncts
```lean
theorem test_prove_exists_by_tendsto_3 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε^2 < δ := by
  prove_exists_by_tendsto

theorem test_prove_exists_by_tendsto_4 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ 2 * ε < δ ∧ ε^3 < δ ∧ |ε| < δ := by
  prove_exists_by_tendsto
```

### Trigonometric Functions
```lean
theorem test_prove_exists_by_tendsto_5 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ sin(ε) < δ := by
  prove_exists_by_tendsto

theorem test_prove_exists_by_tendsto_6 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ (cos(ε) - 1) < δ ∧ sin(ε) < δ := by
  prove_exists_by_tendsto
```

### Complex Expressions
```lean
theorem test_prove_exists_by_tendsto_7 (M : ℝ) (h : 0 < M) : 
  ∃ ε : ℝ, 0 < ε ∧ ε * sin(ε) < M := by
  prove_exists_by_tendsto

theorem test_prove_exists_by_tendsto_8 (bound : ℝ) (h : 0 < bound) : 
  ∃ h : ℝ, 0 < h ∧ h^2 * |sin(h)| < bound ∧ (cos(h) - 1) * h < bound := by
  prove_exists_by_tendsto
```

### Edge Cases
```lean
-- Single inequality with complex expression
theorem test_prove_exists_by_tendsto_9 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ (3 * ε^2 * sin(ε)) < δ := by
  prove_exists_by_tendsto

-- Many conjuncts
theorem test_prove_exists_by_tendsto_10 (δ : ℝ) (h : 0 < δ) : 
  ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε^2 < δ ∧ ε^3 < δ ∧ |ε| < δ ∧ 2 * ε < δ := by
  prove_exists_by_tendsto
```

This algorithm systematically generates a comprehensive test suite by:
1. **Structural enumeration**: Covering all valid goal patterns within complexity bounds
2. **Provability preservation**: Only including expressions that genuinely tend to zero
3. **Comprehensive coverage**: Testing single/multiple inequalities, various function types, different variable names
4. **Scalability**: Parameters control complexity for different testing scenarios
