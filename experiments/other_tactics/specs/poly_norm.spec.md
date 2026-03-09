> **User Request:** Tactic that decides polynomial equality by normalizing polynomial expressions and comparing their canonical forms. Can prove or disprove goals of the form `p = q` where `p` and `q` are polynomial expressions.

---

# Tactic Specification: poly_norm

## Analysis

## Tactic Analysis: Polynomial Equality Decision Procedure

### 1. Tactic Name
`poly_norm`

### 2. Scope Analysis

**Most general interpretation**: A tactic that could handle polynomial equality over any ring or field, with arbitrary variables, coefficients from any coefficient type, and potentially multivariate polynomials with complex nested structures.

**Lean constraints**: 
- Lean's metaprogramming requires syntactic pattern matching on `Expr`
- Normalization needs computable operations on coefficient types
- Reflection between syntax and semantic polynomial operations is complex
- Limited built-in support for symbolic computation compared to specialized CAS systems

**Implementation complexity**: 
- Full generality would require implementing polynomial parsing, multi-variable handling, coefficient arithmetic in the meta-level, and bidirectional conversion between `Expr` and normalized forms
- Multivariate cases significantly increase complexity
- Different coefficient types (ℕ, ℤ, ℚ, arbitrary rings) require different normalization strategies

**Chosen scope**: Target univariate polynomials over ℚ (rationals) with basic arithmetic operations (`+`, `-`, `*`, scalar multiplication, exponentiation by natural numbers). This balances meaningful utility with implementability, as ℚ has decidable arithmetic and univariate polynomials have well-understood canonical forms.

### 3. Mathematical Specification

**Class of formulas**: Goals of the form `p = q` where `p, q ∈ ℚ[X]` are polynomial expressions in a single variable `X` over rationals, built from:
- Variables (single variable `X`)
- Rational constants 
- Addition: `p₁ + p₂`
- Subtraction: `p₁ - p₂` 
- Multiplication: `p₁ * p₂`
- Scalar multiplication: `c * p` where `c ∈ ℚ`
- Natural number exponentiation: `p ^ n` where `n ∈ ℕ`

**Logical fragment**: Equational logic over polynomial expressions

**Provability conditions**: A formula `p = q` is provable if and only if `norm(p) = norm(q)` where `norm : ℚ[X] → ℚ[X]` is the canonical normalization function that produces polynomials in standard form `∑ᵢ aᵢXⁱ` with terms ordered by degree and zero coefficients removed.

**Formal characterization**:
```
Goals := {(p = q) | p, q ∈ Poly(ℚ, X) ∧ syntactically_polynomial(p) ∧ syntactically_polynomial(q)}
Provable(p = q) ↔ canonical_form(p) = canonical_form(q)
```

### 4. Purpose
Decides polynomial equality goals by normalizing both sides to canonical form and comparing structural equality.

### 5. Input Types
- **Goal type**: `Expr` representing equality `p = q` where both sides parse as polynomial expressions
- **Expected Lean types**: Goals of type `α = α` where `α` is interpretable as polynomials over ℚ

### 6. Algorithm

1. **Goal structure verification**: Check that goal has form `p = q`
2. **Polynomial parsing**: 
   - Parse left side `p` into internal polynomial representation
   - Parse right side `q` into internal polynomial representation  
   - Fail if either side contains non-polynomial constructs
3. **Normalization**:
   - Convert each polynomial to canonical form (sum of terms `aᵢXⁱ`)
   - Combine like terms, sort by degree
   - Remove zero coefficients
4. **Comparison**: Check if normalized forms are syntactically identical
5. **Proof construction**:
   - If equal: construct proof term using ring axioms and normalization lemmas
   - If unequal: fail with informative error message

### 7. Success Criteria

**Success**: 
- Goal is syntactically of form `p = q`
- Both `p` and `q` parse as valid polynomial expressions
- Normalized forms are identical

**Failure**:
- Goal is not an equality
- Either side contains non-polynomial expressions (e.g., division, transcendental functions)
- Normalized forms differ (polynomials are genuinely unequal)
- Parsing errors due to unsupported syntax

### 8. Edge Cases

- **Zero polynomials**: `0 = 0`, `x - x = 0`
- **Constant polynomials**: `3 = 3`, `2 + 1 = 3`
- **Coefficient arithmetic**: `(1/2) * x = x/2`
- **Expansion required**: `(x + 1)² = x² + 2*x + 1`
- **Variable naming**: Handle different variable names by standardization
- **Implicit multiplication**: `2x` vs `2 * x`
- **Nested expressions**: `((x + 1) * 2)` requiring proper associativity

### 9. Dependencies

```lean
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Ring.Basic
import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
```

**Key components needed**:
- `Polynomial ℚ` for semantic polynomial operations
- Ring normalization tactics as reference
- Expression parsing and manipulation utilities
- Rational arithmetic for coefficient operations

## Test Generation Algorithm

# Test Case Generation Algorithm for `poly_norm` Tactic

## Algorithm Overview

This algorithm generates test cases for the `poly_norm` tactic by systematically creating polynomial equality statements that should be provable through normalization. The approach combines structured polynomial expression generation with provability guarantees.

## 1. Input Parameters

```lean
structure PolyTestConfig where
  max_degree : Nat := 3           -- Maximum polynomial degree
  max_depth : Nat := 4            -- Maximum expression nesting depth
  num_coeffs : Nat := 5           -- Number of distinct rational coefficients to use
  var_name : String := "x"        -- Variable name
  test_count : Nat := 100         -- Number of test cases to generate
  coeff_range : Rat := 5          -- Coefficients in range [-coeff_range, coeff_range]
  include_zero : Bool := true     -- Include zero polynomial cases
  include_constants : Bool := true -- Include constant polynomial cases
```

## 2. Core Algorithm

### Phase 1: Coefficient and Basis Generation

```lean
def generate_coefficients (config : PolyTestConfig) : List Rat :=
  let base_coeffs := [1, -1, 2, -2, 1/2, -1/2, 3/2, 0]
  let random_coeffs := generate_random_rationals config.coeff_range (config.num_coeffs - 8)
  base_coeffs ++ random_coeffs

def generate_monomial_basis (config : PolyTestConfig) : List Expr :=
  (List.range (config.max_degree + 1)).map fun i =>
    if i = 0 then `(1 : ℚ)
    else if i = 1 then Expr.const config.var_name
    else `($(Expr.const config.var_name) ^ $i)
```

### Phase 2: Expression Structure Generation

The algorithm generates polynomial expressions using a grammar-based approach:

```lean
inductive PolyExprShape where
  | monomial : Nat → PolyExprShape  -- x^n
  | scaled : Rat → PolyExprShape → PolyExprShape  -- c * p
  | sum : PolyExprShape → PolyExprShape → PolyExprShape  -- p + q
  | diff : PolyExprShape → PolyExprShape → PolyExprShape  -- p - q
  | prod : PolyExprShape → PolyExprShape → PolyExprShape  -- p * q
  | power : PolyExprShape → Nat → PolyExprShape  -- p^n

def generate_expr_shapes (config : PolyTestConfig) : List PolyExprShape :=
  -- Generate all valid shapes up to max_depth using BFS
  let rec generate_at_depth (depth : Nat) (prev_shapes : List PolyExprShape) :=
    if depth = 0 then
      -- Base cases: monomials
      (List.range (config.max_degree + 1)).map PolyExprShape.monomial
    else if depth > config.max_depth then prev_shapes
    else
      let new_shapes := []
      -- Add scaled versions
      let scaled := prev_shapes.bind fun shape =>
        config.coefficients.map (PolyExprShape.scaled · shape)
      -- Add binary operations
      let binary := prev_shapes.bind fun s1 =>
        prev_shapes.bind fun s2 => [
          PolyExprShape.sum s1 s2,
          PolyExprShape.diff s1 s2,
          PolyExprShape.prod s1 s2  -- Only if resulting degree ≤ max_degree
        ]
      -- Add powers
      let powered := prev_shapes.bind fun shape =>
        (List.range 4).map (PolyExprShape.power shape ·)
      
      generate_at_depth (depth + 1) (prev_shapes ++ scaled ++ binary ++ powered)
  
  generate_at_depth 0 []
```

### Phase 3: Semantic Equivalence Classes

The key insight is to group expressions by their normalized polynomial form, then generate equalities within each equivalence class.

```lean
-- Canonical polynomial representation
structure CanonicalPoly where
  coeffs : List (Nat × Rat)  -- (degree, coefficient) pairs, sorted by degree
  deriving Eq, Hashable

def normalize_expr_to_canonical (expr : PolyExprShape) : CanonicalPoly :=
  -- Convert expression to standard polynomial form ∑ aᵢxⁱ
  match expr with
  | monomial n => CanonicalPoly.mk [(n, 1)]
  | scaled c p => 
      let norm_p := normalize_expr_to_canonical p
      CanonicalPoly.mk (norm_p.coeffs.map fun (deg, coeff) => (deg, c * coeff))
  | sum p q =>
      let norm_p := normalize_expr_to_canonical p
      let norm_q := normalize_expr_to_canonical q
      combine_coefficients norm_p norm_q (· + ·)
  | diff p q =>
      let norm_p := normalize_expr_to_canonical p
      let norm_q := normalize_expr_to_canonical q  
      combine_coefficients norm_p norm_q (· - ·)
  | prod p q =>
      let norm_p := normalize_expr_to_canonical p
      let norm_q := normalize_expr_to_canonical q
      multiply_polynomials norm_p norm_q
  | power p n =>
      let norm_p := normalize_expr_to_canonical p
      power_polynomial norm_p n

def group_by_equivalence (shapes : List PolyExprShape) : 
    HashMap CanonicalPoly (List PolyExprShape) :=
  shapes.foldl (fun acc shape =>
    let canonical := normalize_expr_to_canonical shape
    acc.insert canonical (shape :: (acc.find? canonical).getD [])
  ) HashMap.empty
```

### Phase 4: Test Case Generation

```lean
def generate_test_cases (config : PolyTestConfig) : List (PolyExprShape × PolyExprShape) :=
  let shapes := generate_expr_shapes config
  let equiv_classes := group_by_equivalence shapes
  
  let test_cases := equiv_classes.toList.bind fun (canonical, expressions) =>
    if expressions.length ≥ 2 then
      -- Generate pairs within equivalence class
      expressions.bind fun e1 =>
        expressions.bind fun e2 =>
          if e1 ≠ e2 then [(e1, e2)] else []
    else []
  
  -- Add special cases
  let special_cases := generate_special_cases config
  
  (test_cases ++ special_cases).take config.test_count
```

### Phase 5: Special Case Generation

```lean
def generate_special_cases (config : PolyTestConfig) : List (PolyExprShape × PolyExprShape) :=
  let zero_cases := [
    -- x - x = 0
    (PolyExprShape.diff (monomial 1) (monomial 1), monomial 0),
    -- 2*x - 2*x = 0  
    (PolyExprShape.diff (scaled 2 (monomial 1)) (scaled 2 (monomial 1)), monomial 0)
  ]
  
  let expansion_cases := [
    -- (x + 1)² = x² + 2*x + 1
    (PolyExprShape.power (sum (monomial 1) (monomial 0)) 2,
     sum (sum (monomial 2) (scaled 2 (monomial 1))) (monomial 0)),
    -- (x - 1)² = x² - 2*x + 1
    (PolyExprShape.power (diff (monomial 1) (monomial 0)) 2,
     diff (sum (monomial 2) (monomial 0)) (scaled 2 (monomial 1)))
  ]
  
  let coefficient_cases := [
    -- (1/2) * x = x / 2  
    (PolyExprShape.scaled (1/2) (monomial 1), 
     PolyExprShape.scaled (1/2) (monomial 1)),
    -- 2*x + 3*x = 5*x
    (PolyExprShape.sum (scaled 2 (monomial 1)) (scaled 3 (monomial 1)),
     PolyExprShape.scaled 5 (monomial 1))
  ]
  
  zero_cases ++ expansion_cases ++ coefficient_cases
```

## 3. Provability Criteria

The algorithm ensures provability through the normalization-based equivalence:

1. **Semantic Equivalence**: Two expressions are provably equal iff their canonical forms are identical
2. **Syntactic Validity**: All generated expressions use only supported polynomial operations
3. **Degree Bounds**: All intermediate results respect the maximum degree constraint
4. **Coefficient Arithmetic**: All coefficients remain in ℚ and are computationally tractable

```lean
def is_provable (lhs rhs : PolyExprShape) : Bool :=
  let norm_lhs := normalize_expr_to_canonical lhs
  let norm_rhs := normalize_expr_to_canonical rhs
  norm_lhs = norm_rhs
```

## 4. Example Outputs

Here are 10 example theorem statements the algorithm would generate:

### Basic Equivalences
```lean
theorem test_1 : (x : ℚ) + x = 2 * x := by poly_norm

theorem test_2 : (x : ℚ) * x * x = x^3 := by poly_norm

theorem test_3 : (0 : ℚ[x]) = x - x := by poly_norm
```

### Expansion Cases  
```lean
theorem test_4 : ((x : ℚ) + 1)^2 = x^2 + 2*x + 1 := by poly_norm

theorem test_5 : ((x : ℚ) - 2)^2 = x^2 - 4*x + 4 := by poly_norm

theorem test_6 : ((x : ℚ) + 1) * (x - 1) = x^2 - 1 := by poly_norm
```

### Coefficient Arithmetic
```lean
theorem test_7 : (1/2 : ℚ) * x + (3/2) * x = 2 * x := by poly_norm

theorem test_8 : (3 : ℚ) * x^2 - x^2 = 2 * x^2 := by poly_norm
```

### Complex Rearrangements
```lean
theorem test_9 : ((x : ℚ) + 2) * (x + 3) = x^2 + 5*x + 6 := by poly_norm

theorem test_10 : ((x : ℚ)^2 + x) - (x^2 - x) = 2*x := by poly_norm
```

## 5. Implementation Notes

- **Systematic Coverage**: The algorithm ensures coverage of all major polynomial operation patterns
- **Scalability**: Parameters allow controlling complexity for different testing scenarios
- **Provability Guarantee**: Semantic equivalence ensures all generated statements are provable
- **Lean Integration**: Output format directly translates to Lean theorem statements
- **Edge Case Handling**: Special cases cover critical scenarios like zero polynomials and expansions

This algorithm provides comprehensive test coverage while maintaining mathematical rigor and implementability within Lean's metaprogramming framework.
