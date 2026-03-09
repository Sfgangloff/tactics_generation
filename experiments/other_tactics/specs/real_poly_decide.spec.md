> **User Request:** A tactic for deciding statements in the first-order theory of real numbers. This handles goals involving real arithmetic with polynomial expressions, inequalities, and basic algebraic operations. It should be capable of proving statements about real polynomial systems and inequalities. The tactic may use lookup tables for common polynomial inequality patterns to improve performance.

---

# Tactic Specification: real_poly_decide

## Analysis

# Tactic Analysis: Real Polynomial Decision Procedure

## 1. Tactic Name
`real_poly_decide`

## 2. Scope Analysis

**Most general interpretation**: A complete decision procedure for the first-order theory of real closed fields (Tarski's theorem), handling arbitrary quantified formulas over polynomial equations and inequalities in real arithmetic.

**Lean constraints**: 
- Lean's metaprogramming operates on syntax trees, requiring pattern matching on expression forms
- No built-in computer algebra system for polynomial manipulation
- Limited reflection capabilities for complex mathematical structures
- Performance constraints for proof term construction
- Need to interface with existing Mathlib polynomial and real number APIs

**Implementation complexity**: Full quantifier elimination for real closed fields is extremely complex, requiring sophisticated algorithms like cylindrical algebraic decomposition. This would be a massive undertaking requiring extensive computer algebra infrastructure.

**Chosen scope**: Quantifier-free formulas in the first-order theory of reals, focusing on polynomial equations and inequalities with rational coefficients. This covers a practically useful subset while remaining implementable through:
- Polynomial normalization and comparison
- Sign analysis and root isolation techniques  
- Case splitting on polynomial signs
- Lookup tables for common patterns (as requested)

## 3. Mathematical Specification

**Class of formulas**: 
```
F = {φ | φ is a quantifier-free Boolean combination of atomic formulas of the form p(x₁,...,xₙ) ~ 0}
```
where:
- `p(x₁,...,xₙ)` is a polynomial with rational coefficients
- `~` ∈ {`=`, `≠`, `<`, `≤`, `>`, `≥`}
- Boolean combinations use `∧`, `∨`, `¬`

**Logical fragment**: Quantifier-free first-order logic over the real closed field structure `⟨ℝ, +, ·, 0, 1, <⟩`

**Provability conditions**: A formula φ ∈ F is provable if and only if it is valid in the real closed field ℝ (i.e., true under all variable assignments). This is decidable by Tarski's theorem, restricted to the quantifier-free case.

**Example formulas**:
- `x² + y² > 0 ∨ (x = 0 ∧ y = 0)`
- `∀ x y : ℝ, x² - 2*x + 1 = (x - 1)²` (after preprocessing to remove universal quantifiers over the goal)

## 4. Purpose
A decision procedure that proves or disproves quantifier-free statements about real polynomial arithmetic involving equations and inequalities.

## 5. Input Types
- **Goals**: `Prop` expressions representing quantifier-free Boolean combinations of polynomial comparisons over `ℝ`
- **Context**: Real-valued variables and polynomial hypotheses in the local context

## 6. Algorithm

1. **Goal Analysis**: Parse the goal to identify the Boolean structure and extract atomic polynomial comparisons

2. **Polynomial Normalization**: 
   - Convert all atomic formulas to the form `p(x₁,...,xₙ) ~ 0`
   - Normalize polynomials to canonical form using Mathlib's polynomial API

3. **Lookup Table Check**: 
   - Check if the normalized formula matches known patterns in lookup tables
   - Return cached proof if found

4. **Sign Analysis**:
   - Identify critical points (roots of all polynomials involved)
   - Construct sign table showing the sign of each polynomial in each interval
   - Use Mathlib's `Polynomial.sign` and interval arithmetic

5. **Case Analysis**:
   - Split into cases based on polynomial signs in different regions
   - For each case, evaluate the truth value of atomic formulas
   - Combine using Boolean logic

6. **Proof Construction**:
   - Build proof term using Mathlib's real arithmetic lemmas
   - Use `norm_num` for rational arithmetic
   - Apply polynomial evaluation and comparison lemmas

## 7. Success Criteria

**Success**: The tactic succeeds when:
- The goal is a valid quantifier-free real polynomial formula
- All polynomials have decidable coefficient types (rationals/integers)
- The formula can be proven true through sign analysis

**Failure**: The tactic fails when:
- The goal contains non-polynomial expressions (transcendental functions, etc.)
- Quantifiers are present in the goal (not just in variable declarations)
- The formula is false/unprovable
- Coefficients are symbolic or undecidable

## 8. Edge Cases

- **Degenerate polynomials**: Handle zero polynomials and constant polynomials specially
- **Strict vs non-strict inequalities**: Careful handling of boundary cases at roots
- **Multiple variables**: Ensure proper variable ordering and substitution
- **Large polynomials**: Implement degree and size limits to prevent timeout
- **Numerical stability**: Use exact rational arithmetic to avoid floating-point errors
- **Empty solution sets**: Handle contradictory constraint systems gracefully

## 9. Dependencies

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Sign
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearArithmetic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Polynomial.Basic
```

The implementation would leverage Mathlib's extensive polynomial library and real number theory, building upon existing tactics like `norm_num` and `linarith` for the foundational arithmetic reasoning.

## Test Generation Algorithm

# Test Case Generation Algorithm for `real_poly_decide`

## 1. Input Parameters

```lean
structure PolyTestConfig where
  max_variables : Nat := 3           -- Maximum number of variables (x, y, z, ...)
  max_degree : Nat := 3              -- Maximum polynomial degree
  max_terms : Nat := 4               -- Maximum terms per polynomial
  max_depth : Nat := 3               -- Maximum Boolean nesting depth
  coeff_range : Int := 5             -- Coefficients in [-coeff_range, coeff_range]
  num_samples : Nat := 100           -- Number of test cases to generate
  complexity_levels : List Nat := [1, 2, 3]  -- Complexity progression
```

## 2. Core Algorithm

### Phase 1: Polynomial Generation

```lean
-- Generate atomic polynomials with controlled complexity
def generate_polynomial (vars : List String) (degree : Nat) (terms : Nat) : Polynomial :=
  -- Use systematic enumeration of monomial structures
  -- For degree d, variables [x,y], generate: x^d, x^(d-1)*y, ..., y^d
  -- Then assign random rational coefficients from [-coeff_range, coeff_range]
```

**Polynomial Templates by Complexity:**

1. **Level 1 (Linear)**: `a*x + b`, `a*x + b*y + c`
2. **Level 2 (Quadratic)**: `x^2 + a*x + b`, `x^2 + y^2 + a`
3. **Level 3 (Mixed)**: `x^2*y + a*x + b*y + c`, `x^3 + a*x^2 + b*x + c`

### Phase 2: Atomic Formula Generation

```lean
inductive ComparisonOp
| eq | ne | lt | le | gt | ge

def generate_atomic (poly : Polynomial) (op : ComparisonOp) : AtomicFormula :=
  -- Convert to standard form: p(x,y,...) ~ 0
  match op with
  | eq => poly = 0
  | lt => poly < 0
  | ge => poly ≥ 0
  -- etc.
```

**Systematic Atomic Generation:**
- For each polynomial `p`, generate all 6 comparison operators
- Focus on "interesting" cases: where polynomial changes sign
- Include degenerate cases: constant polynomials, zero polynomial

### Phase 3: Boolean Structure Generation

```lean
inductive BoolFormula
| atom : AtomicFormula → BoolFormula  
| and : BoolFormula → BoolFormula → BoolFormula
| or : BoolFormula → BoolFormula → BoolFormula
| not : BoolFormula → BoolFormula

-- Generate using grammar-based enumeration
def generate_bool_structure (depth : Nat) (num_atoms : Nat) : List BoolFormula :=
  -- Enumerate all valid parse trees up to given depth
  -- Use Catalan numbers for binary tree structures
  -- Ensure balanced representation of ∧, ∨, ¬
```

**Boolean Templates by Depth:**

1. **Depth 1**: Single atoms `p(x) > 0`
2. **Depth 2**: `p(x) > 0 ∧ q(x) < 0`, `p(x) = 0 ∨ q(x) ≠ 0`  
3. **Depth 3**: `(p(x) > 0 ∧ q(x) > 0) ∨ r(x) = 0`

### Phase 4: Provability Filtering

This is the crucial step - we must only generate theorems that are **always true**.

```lean
def is_provably_valid (formula : BoolFormula) : Bool :=
  -- Use multiple validation strategies:
  
  -- Strategy 1: Symbolic patterns (lookup table)
  if matches_known_valid_pattern(formula) then true
  
  -- Strategy 2: Algebraic identities
  else if is_algebraic_identity(formula) then true
  
  -- Strategy 3: Sign analysis sampling
  else sample_based_validation(formula)
```

**Known Valid Patterns (Lookup Table):**

1. **Tautologies**: 
   - `p(x) ≥ 0 ∨ p(x) < 0` (excluded middle)
   - `p(x)^2 ≥ 0` (squares non-negative)
   - `p(x) = 0 ∧ p(x) ≠ 0 → False` (contradiction)

2. **Algebraic identities**:
   - `(x - a)^2 = x^2 - 2*a*x + a^2`
   - `x^2 - y^2 = (x-y)*(x+y)`

3. **Monotonicity patterns**:
   - `x > 0 ∧ y > 0 → x + y > 0`
   - `x > y ∧ y > z → x > z`

**Sample-Based Validation:**
```lean
def sample_based_validation (formula : BoolFormula) : Bool :=
  -- Generate systematic test points covering critical regions
  let critical_points := find_all_roots(extract_polynomials(formula))
  let test_intervals := partition_real_line(critical_points)
  
  -- Test formula on representative points from each interval
  test_intervals.all (fun interval => 
    let test_point := interval.representative_point
    evaluate_formula(formula, test_point) = True)
```

### Phase 5: Theorem Assembly

```lean
def generate_theorem (formula : BoolFormula) (context : Context) : String :=
  match context with
  | no_context => 
    s!"theorem auto_test_{id} : {formula_to_lean(formula)} := by real_poly_decide"
  | with_hypotheses hyps =>
    s!"theorem auto_test_{id} {format_vars(formula)} {format_hyps(hyps)} : 
       {formula_to_lean(formula)} := by real_poly_decide"
```

## 3. Provability Criteria

### Tier 1: Guaranteed Valid (High Priority)

1. **Perfect Squares**: `x^2 + y^2 ≥ 0`, `(x-1)^2 ≥ 0`
2. **Factored Forms**: `x^2 - 1 = (x-1)*(x+1)`  
3. **Polynomial Expansions**: `(x+y)^2 = x^2 + 2*x*y + y^2`
4. **Sign Definite**: Sum of squares expressions

### Tier 2: Algorithmically Verified (Medium Priority)

1. **Interval Analysis**: Formulas true on all real intervals
2. **Derivative Tests**: Using monotonicity properties
3. **Sturm Sequences**: For counting real roots

### Tier 3: Empirically Sampled (Lower Priority)

1. **Dense Sampling**: Test on many random points
2. **Boundary Analysis**: Focus on polynomial roots
3. **Asymptotic Behavior**: Check limits at ±∞

## 4. Example Outputs

Here are 10 example theorem statements the algorithm would generate:

```lean
-- Tier 1: Perfect squares and basic identities
theorem auto_test_001 : ∀ x : ℝ, x^2 ≥ 0 := by real_poly_decide

theorem auto_test_002 : ∀ x y : ℝ, x^2 + y^2 ≥ 0 := by real_poly_decide

theorem auto_test_003 : ∀ x : ℝ, (x - 1)^2 = x^2 - 2*x + 1 := by real_poly_decide

-- Tier 1: Disjunctive tautologies  
theorem auto_test_004 : ∀ x : ℝ, x > 0 ∨ x ≤ 0 := by real_poly_decide

theorem auto_test_005 : ∀ x y : ℝ, x^2 + y^2 > 0 ∨ (x = 0 ∧ y = 0) := by real_poly_decide

-- Tier 2: Factorization and algebraic manipulation
theorem auto_test_006 : ∀ x : ℝ, x^2 - 4 = 0 ↔ (x = 2 ∨ x = -2) := by real_poly_decide

theorem auto_test_007 : ∀ x y : ℝ, (x + y)^2 ≥ 4*x*y := by real_poly_decide

-- Tier 2: Monotonicity and ordering
theorem auto_test_008 : ∀ x : ℝ, x > 1 → x^2 > 1 := by real_poly_decide

theorem auto_test_009 : ∀ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x + y = 0 → x = 0 ∧ y = 0 := by real_poly_decide

-- Tier 3: Complex Boolean combinations
theorem auto_test_010 : ∀ x : ℝ, (x^3 - x = 0) ↔ (x = 0 ∨ x = 1 ∨ x = -1) := by real_poly_decide
```

## 5. Implementation Strategy

1. **Start Simple**: Begin with Tier 1 formulas (guaranteed valid patterns)
2. **Expand Systematically**: Add complexity gradually while maintaining high success rate
3. **Validate Extensively**: Use multiple verification methods for each generated formula
4. **Maintain Statistics**: Track success/failure rates to tune generation parameters
5. **Cache Results**: Store validated patterns for faster future generation

This algorithm ensures comprehensive coverage of the `real_poly_decide` tactic's intended scope while maintaining high confidence that generated theorems are actually provable.
