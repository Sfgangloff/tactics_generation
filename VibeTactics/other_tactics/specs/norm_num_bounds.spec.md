> **User Request:** A tactic that proves numerical approximations of real-valued expressions by computing bounds. Given a goal of the form `a < expr < b` where `expr` is a real-valued expression involving constants like π, e, ln, exp, sin, cos, etc., the tactic computes numerical approximations with sufficient precision to prove the inequality. The tactic should handle arithmetic operations (+, -, *, /, ^) and common mathematical functions (exp, log, trigonometric functions) on real numbers. It works by evaluating the expression using interval arithmetic or computable reals to establish tight enough bounds that prove the target inequality. Example usage: proving goals like `3.83 < ln(2) + π < 3.84` or `2.7 < e < 2.8`.

---

# Tactic Specification: norm_num_bounds

## Analysis

# Tactic Analysis: Numerical Approximation Bounds

## 1. Tactic Name
`norm_num_bounds`

## 2. Scope Analysis

### Most general interpretation
The broadest interpretation would handle any inequality involving real-valued expressions with arbitrary mathematical functions, infinite precision arithmetic, and symbolic manipulation of transcendental numbers.

### Lean constraints
- Lean 4's computational capabilities are limited to decidable/computable operations
- Transcendental functions like π, e, ln, sin, cos are not computationally tractable without approximation
- Expression matching must work with Lean's syntax trees
- Proof construction requires constructive evidence (witness bounds)
- Limited precision arithmetic in the underlying system

### Implementation complexity
Full symbolic computation with arbitrary precision would be extremely complex. Interval arithmetic libraries would need to be implemented or interfaced. The tactic would need sophisticated expression evaluation and error propagation.

### Chosen scope
Target expressions built from:
- Rational number literals
- Basic arithmetic operations (+, -, *, /)
- A limited set of mathematical constants (π, e) 
- A limited set of functions (ln, exp, sin, cos, sqrt)
- Integer powers (^)

Use fixed-precision interval arithmetic with enough precision to prove the given bounds. This balances practical utility with implementability while avoiding the complexity of full symbolic computation.

## 3. Mathematical Specification

**Formula class**: Goals of the form `a < E < b` where:
- `a, b ∈ ℚ` (rational bounds)
- `E` is a real-valued expression in the grammar:
  ```
  E ::= q (rational literal)
      | π | e 
      | E₁ + E₂ | E₁ - E₂ | E₁ * E₂ | E₁ / E₂
      | E^n (where n ∈ ℤ)
      | ln(E) | exp(E) | sin(E) | cos(E) | sqrt(E)
  ```

**Logical fragment**: Ground arithmetic formulas over ℝ with transcendental functions.

**Provability conditions**: A formula `a < E < b` is provable by this tactic if and only if there exists a computational interval arithmetic evaluation that produces bounds `[l, u]` for `E` such that `a < l` and `u < b`, where the computation uses sufficient precision to guarantee soundness.

**Example**: `3.83 < ln(2) + π < 3.84` is provable if interval evaluation of `ln(2) + π` yields bounds contained in `(3.83, 3.84)`.

## 4. Purpose
Proves numerical inequalities involving real-valued expressions by computing rigorous interval arithmetic bounds.

## 5. Input Types
- **Goal**: `Prop` of the form `a < expr < b` where `a b : ℚ` and `expr : ℝ`
- **Alternative forms**: `a ≤ expr ≤ b`, `expr < b`, `a < expr`, etc.

## 6. Algorithm

1. **Goal parsing**: Match goal against patterns `a < E < b`, `a ≤ E ≤ b`, etc.
2. **Expression analysis**: 
   - Traverse the expression tree of `E`
   - Verify all components are in the supported grammar
   - Identify required mathematical constants and functions
3. **Precision estimation**: Estimate required precision based on target bound width
4. **Interval evaluation**:
   - Recursively evaluate sub-expressions using interval arithmetic
   - Propagate uncertainty through operations
   - Handle function evaluations (ln, exp, sin, cos) with rigorous bounds
5. **Bound checking**: Verify computed interval `[l, u]` satisfies `a < l` and `u < b`
6. **Proof construction**: Generate proof term using Mathlib's interval arithmetic lemmas and computational reflection

## 7. Success Criteria

**Success**: When interval arithmetic computation produces bounds `[l, u]` for the expression such that the target inequality is satisfied with margin for computational error.

**Failure conditions**:
- Expression contains unsupported functions/operations
- Required precision exceeds implementation limits  
- Computed bounds are too loose to prove the target inequality
- Division by interval containing zero
- Function evaluation outside domain (e.g., ln of negative number)

## 8. Edge Cases

- **Division by zero**: Check denominators don't contain zero in their interval
- **Function domains**: Verify ln, sqrt arguments are positive; handle sin/cos periodicity
- **Precision limits**: Graceful failure when required precision is too high
- **Degenerate intervals**: Handle point intervals and empty intervals
- **Mixed inequality types**: Support ≤, <, >, ≥ combinations
- **Negative numbers**: Proper handling of negative bases with fractional exponents

## 9. Dependencies

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Computability.Float
```

The tactic would extend `norm_num` infrastructure and potentially require custom interval arithmetic implementation or bindings to external libraries for rigorous floating-point computation.

## Test Generation Algorithm

# Test Case Generation Algorithm for `norm_num_bounds`

## 1. Input Parameters

```lean
structure BoundsTestConfig where
  max_depth : Nat := 4              -- Maximum nesting depth of expressions
  num_constants : Nat := 3          -- Number of mathematical constants to include
  num_rationals : Nat := 5          -- Number of rational literals per test
  precision_digits : Nat := 10      -- Decimal precision for bound computation
  bound_margin : Float := 0.01      -- Safety margin for provable bounds
  num_tests_per_shape : Nat := 20   -- Tests generated per expression shape
  inequality_types : List IneqType := [Strict, NonStrict, Mixed]
```

## 2. Core Algorithm

### Phase 1: Expression Structure Generation

**Step 1.1: Enumerate Expression Shapes**
```lean
inductive ExprShape where
  | Rational : ExprShape
  | Constant : ConstType → ExprShape  -- π, e
  | BinOp : BinOpType → ExprShape → ExprShape → ExprShape  -- +, -, *, /
  | UnaryFun : FunType → ExprShape → ExprShape  -- ln, exp, sin, cos, sqrt
  | Power : ExprShape → Int → ExprShape  -- E^n

-- Generate all shapes up to max_depth using recursive enumeration
def generateShapes (max_depth : Nat) : List ExprShape :=
  let rec go (depth : Nat) : List ExprShape :=
    if depth = 0 then
      [ExprShape.Rational] ++ (constants.map ExprShape.Constant)
    else
      let smaller := go (depth - 1)
      let binary := do
        op ← [Add, Sub, Mul, Div]
        left ← smaller
        right ← smaller
        return BinOp op left right
      let unary := do
        fun ← [Ln, Exp, Sin, Cos, Sqrt]
        arg ← smaller
        return UnaryFun fun arg
      let powers := do
        base ← smaller
        exp ← [-3, -2, -1, 2, 3, 4, 5]  -- Exclude 0, 1 for non-triviality
        return Power base exp
      smaller ++ binary ++ unary ++ powers
  go max_depth
```

**Step 1.2: Filter Feasible Shapes**
Remove shapes that are inherently problematic:
- Division where denominator could be zero
- `ln` or `sqrt` of expressions that could be negative
- Extremely deep nesting that would cause precision issues

### Phase 2: Concrete Value Assignment

**Step 2.1: Sample Rational Values**
```lean
-- Generate rational test values with controlled denominators
def sampleRationals (n : Nat) : List Rat :=
  let basic := [0, 1, -1, 1/2, -1/2, 2, -2, 1/3, 2/3, 3/2]
  let random := -- Generate rationals with small denominators (≤ 100)
    List.range 50 |>.bind fun i =>
      List.range 20 |>.map fun d => (i : Int) / (d + 1 : Int)
  (basic ++ random).take n
```

**Step 2.2: Instantiate Expression Shapes**
For each shape, substitute rational values at leaf positions:
```lean
def instantiateShape (shape : ExprShape) (rationals : List Rat) : List RealExpr :=
  -- Recursively replace Rational nodes with concrete values
  -- Use different rational values for different positions
  -- Generate multiple instantiations by varying the assignments
```

### Phase 3: Bound Computation and Verification

**Step 3.1: Interval Arithmetic Evaluation**
```lean
-- Compute rigorous interval bounds for expressions
def evaluateInterval (expr : RealExpr) (precision : Nat) : Option Interval :=
  match expr with
  | RealExpr.rat q => some ⟨q, q⟩  -- Point interval
  | RealExpr.pi => some ⟨3.141592653, 3.141592654⟩  -- Known π bounds
  | RealExpr.e => some ⟨2.718281828, 2.718281829⟩   -- Known e bounds
  | RealExpr.add e1 e2 => 
      do i1 ← evaluateInterval e1 precision
         i2 ← evaluateInterval e2 precision
         some (intervalAdd i1 i2)
  | RealExpr.ln e => 
      do i ← evaluateInterval e precision
         if i.lower ≤ 0 then none  -- Invalid domain
         else some (intervalLn i precision)
  -- ... similar for other operations
```

**Step 3.2: Generate Provable Bounds**
```lean
def generateProvableBounds (expr : RealExpr) (margin : Float) : Option (Rat × Rat) :=
  do interval ← evaluateInterval expr precision_digits
     let lower_bound := interval.lower - margin
     let upper_bound := interval.upper + margin
     -- Convert to rationals with appropriate precision
     some ⟨floatToRat lower_bound, floatToRat upper_bound⟩
```

### Phase 4: Theorem Statement Construction

**Step 4.1: Inequality Type Selection**
```lean
inductive IneqType where
  | Strict : IneqType      -- a < expr < b  
  | NonStrict : IneqType   -- a ≤ expr ≤ b
  | Mixed : IneqType       -- a < expr ≤ b or a ≤ expr < b
  | OneSided : IneqType    -- expr < b or a < expr
```

**Step 4.2: Statement Generation**
```lean
def generateTheoremStatement (expr : RealExpr) (bounds : Rat × Rat) (ineq_type : IneqType) : String :=
  match ineq_type with
  | IneqType.Strict => 
      s!"theorem test_bounds : {bounds.1} < {exprToString expr} ∧ {exprToString expr} < {bounds.2} := by norm_num_bounds"
  | IneqType.NonStrict =>
      s!"theorem test_bounds : {bounds.1} ≤ {exprToString expr} ∧ {exprToString expr} ≤ {bounds.2} := by norm_num_bounds"
  -- ... other cases
```

## 3. Provability Criteria

A generated theorem is considered provable if:

1. **Domain Validity**: All function applications are in valid domains
   - `ln(x)` where x > 0
   - `sqrt(x)` where x ≥ 0
   - No division by zero

2. **Precision Sufficiency**: The computed interval bounds have sufficient precision
   - Interval width < bound_margin / 2
   - No overflow in intermediate computations

3. **Bound Safety**: Generated bounds have adequate margin
   - `computed_lower + margin < stated_lower_bound`
   - `stated_upper_bound < computed_upper - margin`

4. **Computational Feasibility**: Expression can be evaluated without excessive computation
   - Function evaluations converge within iteration limits
   - No transcendental number computations beyond available precision

## 4. Example Outputs

The algorithm would generate theorems like:

```lean
-- Simple arithmetic bounds
theorem test_001 : (3 : ℚ) < (7 : ℝ) / 2 ∧ (7 : ℝ) / 2 < (4 : ℚ) := by norm_num_bounds

-- Transcendental constants  
theorem test_002 : (3.14 : ℚ) < π ∧ π < (3.15 : ℚ) := by norm_num_bounds

-- Function compositions
theorem test_003 : (0.69 : ℚ) < ln(2) ∧ ln(2) < (0.70 : ℚ) := by norm_num_bounds

-- Mixed operations
theorem test_004 : (6.28 : ℚ) < 2 * π ∧ 2 * π < (6.29 : ℚ) := by norm_num_bounds

-- Complex expressions
theorem test_005 : (4.81 : ℚ) ≤ ln(2) + π + 1/2 ∧ ln(2) + π + 1/2 ≤ (4.82 : ℚ) := by norm_num_bounds

-- Power operations
theorem test_006 : (1.41 : ℚ) < sqrt(2) ∧ sqrt(2) < (1.42 : ℚ) := by norm_num_bounds

-- Trigonometric bounds
theorem test_007 : (-0.85 : ℚ) < sin(1) ∧ sin(1) < (-0.84 : ℚ) := by norm_num_bounds

-- One-sided bounds
theorem test_008 : exp(1) < (2.72 : ℚ) := by norm_num_bounds

-- Rational expressions
theorem test_009 : (0.33 : ℚ) < (1 : ℝ) / 3 ∧ (1 : ℝ) / 3 < (0.34 : ℚ) := by norm_num_bounds

-- Nested functions
theorem test_010 : (1.76 : ℚ) < exp(ln(2) + ln(3)) ∧ exp(ln(2) + ln(3)) < (1.77 : ℚ) := by norm_num_bounds
```

This systematic approach ensures comprehensive coverage of the tactic's capabilities while maintaining provability guarantees through rigorous interval arithmetic and safety margins.
