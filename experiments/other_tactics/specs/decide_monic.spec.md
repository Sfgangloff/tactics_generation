> **User Request:** Tactic that decides whether a polynomial is monic (has leading coefficient 1). Can prove or disprove goals of the form `Monic p` where `p` is a polynomial expression by computing its leading coefficient.

---

# Tactic Specification: decide_monic

## Analysis

# Tactic Analysis: Monic Polynomial Decision Procedure

## 1. Tactic Name
`decide_monic`

## 2. Scope Analysis

**Most general interpretation**: A tactic that could handle any goal involving monic polynomials, including complex logical combinations, quantified statements, and arbitrary polynomial expressions in any form.

**Lean constraints**: 
- Lean's metaprogramming requires syntactic pattern matching on expressions
- Computing leading coefficients requires the polynomial to be in a recognizable form or reducible to normal form
- Decidability requires that coefficient computations terminate and are computable
- Limited to polynomial types that have computational support in Mathlib

**Implementation complexity**: 
- Full generality would require a complete polynomial algebra system
- Handling arbitrary polynomial expressions would need sophisticated normalization
- Supporting all coefficient rings would require extensive type class reasoning

**Chosen scope**: Target goals of the form `Monic p` where `p` is a polynomial expression that can be computationally normalized to extract its leading coefficient. Focus on polynomials over decidable rings where coefficient equality is decidable. This balances practical utility with implementational feasibility while covering the most common use cases.

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `Monic p` where:
- `p : Polynomial R` for some ring `R`
- `R` has decidable equality on coefficients
- `p` is either in normal form or reducible to normal form via `simp`/`norm_cast`

**Logical fragment**: Ground atomic formulas in the theory of polynomial rings

**Provability conditions**: 
- `Monic p` is provable iff the leading coefficient of `p` equals `1` in `R`
- `¬(Monic p)` is provable iff the leading coefficient of `p` is computable and not equal to `1`, or if `p = 0`

**Formal characterization**: 
```
Goals := {Monic p | p : Polynomial R, DecidableEq R, p.leadingCoeff is computable}
Provable := {Monic p ∈ Goals | p.leadingCoeff = 1}
Disprovable := {Monic p ∈ Goals | p.leadingCoeff ≠ 1 ∨ p = 0}
```

## 4. Purpose
Automatically proves or disproves goals asserting that a polynomial is monic by computing and checking its leading coefficient.

## 5. Input Types
- **Goal type**: `Monic p` where `p : Polynomial R`
- **Required instances**: `[Ring R] [DecidableEq R]` (or appropriate subclasses)
- **Context**: No specific hypotheses required

## 6. Algorithm

1. **Goal pattern matching**: Check that the goal has the form `Monic ?p`
2. **Type inference**: Extract the polynomial `p` and its coefficient ring `R`
3. **Instance checking**: Verify that `R` has decidable equality
4. **Normalization**: Use `simp` or `norm_cast` to reduce `p` to a form where the leading coefficient is computable
5. **Coefficient extraction**: Compute `p.leadingCoeff` using Lean's evaluation mechanisms
6. **Decision**: 
   - If `p.leadingCoeff = 1`: construct proof using `Polynomial.monic_of_leadingCoeff_eq_one`
   - If `p.leadingCoeff ≠ 1` or `p = 0`: construct counterexample using `Polynomial.not_monic_of_leadingCoeff_ne_one`
7. **Proof construction**: Apply the appropriate theorem with the computed coefficient value

## 7. Success Criteria

**Success conditions**:
- Goal matches pattern `Monic p`
- Polynomial type has decidable coefficient ring
- Leading coefficient is computable
- Computed coefficient is definitionally equal to `1` (proves monic) or definitionally not equal to `1` (disproves monic)

**Failure conditions**:
- Goal is not of the form `Monic p`
- Coefficient ring lacks decidable equality
- Leading coefficient computation doesn't terminate or fails
- Polynomial is in a form that cannot be normalized

## 8. Edge Cases

- **Zero polynomial**: `Monic 0` is false (zero has no leading term)
- **Constant polynomials**: Handle `Monic (C r)` where `r` is a ring element
- **Variable coefficients**: Fail gracefully when coefficients contain unresolved variables
- **Complex expressions**: May need multiple normalization strategies
- **Different ring types**: Handle various coefficient rings (ℕ, ℤ, ℚ, finite fields, etc.)
- **Definitional vs propositional equality**: Ensure the decision procedure works with Lean's definitional equality

## 9. Dependencies

```lean
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Simp
```

**Key theorems likely needed**:
- `Polynomial.monic_iff_leadingCoeff_eq_one`
- `Polynomial.not_monic_zero`
- `Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot`

## Test Generation Algorithm

# Test Case Generation Algorithm for `decide_monic` Tactic

## 1. Input Parameters

```lean
structure MonicTestConfig where
  max_degree : Nat := 5           -- Maximum polynomial degree
  coefficient_rings : List Type := [ℕ, ℤ, ℚ]  -- Ring types to test
  num_variables : Nat := 3        -- Maximum number of polynomial variables (X, Y, Z)
  include_zero : Bool := true     -- Include zero polynomial tests
  include_constants : Bool := true -- Include constant polynomial tests
  complexity_levels : List Nat := [1, 2, 3]  -- Polynomial expression complexity
  num_tests_per_config : Nat := 10 -- Tests per parameter combination
```

## 2. Core Algorithm

### Phase 1: Polynomial Expression Generation

```lean
def generatePolynomialExpressions (config : MonicTestConfig) : List PolynomialExpr :=
  let basePolynomials := generateBasePolynomials config
  let compositePolynomials := generateCompositePolynomials config basePolynomials
  basePolynomials ++ compositePolynomials

-- Base polynomial forms
def generateBasePolynomials (config : MonicTestConfig) : List PolynomialExpr :=
  let forms := []
  -- 1. Constant polynomials: C r
  let constants := if config.include_constants then
    [C 0, C 1, C 2, C (-1)] else []
  -- 2. Monomials: a * X^n
  let monomials := List.range config.max_degree |>.bind fun d =>
    [1, 2, -1, 0].map fun coeff => coeff • X^d
  -- 3. Simple polynomials: X^n + lower terms
  let simple := List.range config.max_degree |>.bind fun d =>
    if d > 0 then [X^d + (d : Polynomial R), X^d - 1] else []
  constants ++ monomials ++ simple

-- Composite polynomial forms (operations on base polynomials)
def generateCompositePolynomials (config : MonicTestConfig) (base : List PolynomialExpr) : List PolynomialExpr :=
  let level1 := base.bind fun p => [p + 1, p - 1, 2 • p, p * p]
  let level2 := if 2 ∈ config.complexity_levels then
    base.bind fun p1 => base.bind fun p2 => [p1 + p2, p1 * p2, p1 - p2]
  else []
  let level3 := if 3 ∈ config.complexity_levels then
    [(X + 1) * (X - 1), (X^2 + X + 1), (2*X + 1)^2]
  else []
  level1 ++ level2 ++ level3
```

### Phase 2: Provability Classification

```lean
def classifyMonicity (p : PolynomialExpr) (R : Type) : MonicityStatus :=
  match computeLeadingCoefficient p R with
  | some coeff => 
    if coeff = 1 then MonicityStatus.Monic
    else if coeff = 0 then MonicityStatus.Zero
    else MonicityStatus.NotMonic coeff
  | none => MonicityStatus.Undecidable

inductive MonicityStatus
  | Monic                    -- Leading coefficient is 1
  | NotMonic (coeff : R)     -- Leading coefficient is coeff ≠ 1
  | Zero                     -- Zero polynomial
  | Undecidable             -- Cannot determine computationally

-- Compute leading coefficient by pattern matching and simplification
def computeLeadingCoefficient (p : PolynomialExpr) (R : Type) : Option R :=
  match p with
  | C r => some r  -- Constant polynomial has leading coeff r
  | X => some 1    -- X has leading coeff 1
  | X^n => some 1  -- X^n has leading coeff 1
  | r • q => (computeLeadingCoefficient q R).map (· * r)
  | p + q => combineAddition (computeLeadingCoefficient p R) (computeLeadingCoefficient q R)
  | p * q => combineMultiplication (computeLeadingCoefficient p R) (computeLeadingCoefficient q R)
  | _ => none      -- Complex expressions need normalization
```

### Phase 3: Test Case Generation

```lean
def generateTestCases (config : MonicTestConfig) : List TestCase :=
  config.coefficient_rings.bind fun R =>
    let polynomials := generatePolynomialExpressions config
    let classified := polynomials.map fun p => (p, classifyMonicity p R)
    let decidable := classified.filter (fun (_, status) => status ≠ MonicityStatus.Undecidable)
    decidable.map (generateTestCase R)

def generateTestCase (R : Type) (p : PolynomialExpr, status : MonicityStatus) : TestCase :=
  match status with
  | MonicityStatus.Monic => 
    { statement := `(Monic $(polynomialToExpr p R))
    , expected := TestResult.Success
    , description := s!"Monic polynomial: {p}"
    }
  | MonicityStatus.NotMonic coeff =>
    { statement := `(Monic $(polynomialToExpr p R))
    , expected := TestResult.Failure
    , description := s!"Non-monic polynomial: {p} (leading coeff: {coeff})"
    }
  | MonicityStatus.Zero =>
    { statement := `(Monic $(polynomialToExpr p R))
    , expected := TestResult.Failure  
    , description := s!"Zero polynomial"
    }
```

## 3. Provability Criteria

A generated test case `Monic p` is:

**Provably True** iff:
- `p.leadingCoeff` is computationally equal to `1` in `R`
- `p ≠ 0` (non-zero polynomial)
- The computation terminates within reasonable bounds

**Provably False** iff:
- `p.leadingCoeff` is computationally equal to some `r ≠ 1` in `R`, OR
- `p = 0` (zero polynomial is never monic)
- The computation terminates within reasonable bounds

**Undecidable** (filtered out):
- Leading coefficient involves unresolved variables
- Computation doesn't terminate or requires complex simplification
- Coefficient ring lacks decidable equality

## 4. Systematic Enumeration Strategy

```lean
def systematicGeneration : TestGenerationStrategy :=
  -- 1. Enumerate by polynomial structure complexity
  for complexity in [1, 2, 3] do
    -- 2. For each coefficient ring
    for R in [ℕ, ℤ, ℚ] do
      -- 3. Generate polynomials of each degree
      for degree in [0, 1, 2, 3, 4, 5] do
        -- 4. Vary leading coefficients systematically
        for leadingCoeff in [0, 1, 2, -1, 3] do
          -- 5. Add random lower-degree terms
          generateWithLeadingCoeff degree leadingCoeff R complexity
```

## 5. Example Test Cases Generated

### Basic Monic Cases (Should Succeed)
1. `theorem test_monic_x : Monic (X : Polynomial ℤ) := by decide_monic`
2. `theorem test_monic_x_squared : Monic (X^2 : Polynomial ℚ) := by decide_monic`  
3. `theorem test_monic_x_plus_const : Monic (X^3 + 2*X + 1 : Polynomial ℕ) := by decide_monic`
4. `theorem test_monic_factored : Monic ((X + 1) * (X - 1) : Polynomial ℤ) := by decide_monic`

### Non-Monic Cases (Should Fail Constructively)
5. `theorem test_not_monic_const : ¬Monic (2 : Polynomial ℕ) := by decide_monic`
6. `theorem test_not_monic_scaled : ¬Monic (2*X^2 + X + 1 : Polynomial ℤ) := by decide_monic`
7. `theorem test_not_monic_zero : ¬Monic (0 : Polynomial ℚ) := by decide_monic`

### Edge Cases
8. `theorem test_monic_high_degree : Monic (X^10 + X^9 + X^8 + 1 : Polynomial ℤ) := by decide_monic`
9. `theorem test_monic_after_expansion : Monic ((X + 1)^2 - 2*X - 1 : Polynomial ℚ) := by decide_monic`
10. `theorem test_not_monic_complex : ¬Monic (3*X^4 - 2*X^3 + X - 5 : Polynomial ℤ) := by decide_monic`

### Generated Test Structure
```lean
structure TestCase where
  ring_type : Type
  polynomial_expr : String  -- Human readable form
  lean_statement : String   -- Actual Lean code
  expected_result : Bool    -- true if should be monic
  leading_coefficient : String
  complexity_level : Nat
  test_category : String    -- "basic", "edge_case", "composite", etc.
```

This algorithm ensures comprehensive coverage of the `decide_monic` tactic's scope while maintaining provability guarantees through computational verification of leading coefficients.
