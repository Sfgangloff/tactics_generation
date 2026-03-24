> **User Request:** Tactic that computes the coefficient of a specific degree term in a polynomial expression. Can simplify expressions of the form `coeff p n` where `p` is a polynomial and `n` is the degree, reducing them to their numerical value.

---

# Tactic Specification: poly_coeff

## Analysis

# Tactic Analysis: Polynomial Coefficient Computation

## 1. Tactic Name
`poly_coeff`

## 2. Scope Analysis

**Most general interpretation**: A tactic that can evaluate any expression involving polynomial coefficients, potentially handling multivariate polynomials, coefficients over arbitrary rings, symbolic degree expressions, and complex nested coefficient operations.

**Lean constraints**: 
- Polynomial coefficient computation requires decidable equality and computable operations on the coefficient ring
- Expression matching is limited to syntactic patterns we can recognize
- We need access to Mathlib's polynomial API and coefficient evaluation functions
- Normalization may require canonical forms that aren't always available

**Implementation complexity**: 
- Full generality would require sophisticated expression analysis and symbolic computation
- Handling all possible polynomial representations and coefficient ring types adds significant complexity
- Dynamic degree evaluation and multivariate cases exponentially increase difficulty

**Chosen scope**: Target univariate polynomials over computable rings (ℕ, ℤ, ℚ, finite fields) where:
- The polynomial is given in a form Lean can evaluate (concrete terms or simple symbolic expressions)
- The degree is a concrete natural number or simple expression reducible to one
- The goal is a definitional equality `Polynomial.coeff p n = k` where `k` is the expected coefficient value

This balances practical utility with implementation feasibility while covering the most common use cases in mathematical proofs.

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `Polynomial.coeff p n = c` where:
- `p : Polynomial R` for some computable ring `R`
- `n : ℕ` is reducible to a concrete natural number
- `c : R` is the expected coefficient value

**Logical fragment**: Equational reasoning in dependent type theory with decidable equality on coefficient rings.

**Provability conditions**: A formula `Polynomial.coeff p n = c` has a proof if and only if:
1. `p` can be reduced to a canonical polynomial form
2. `n` can be reduced to a concrete natural number `k`
3. The coefficient of degree `k` in the canonical form of `p` is definitionally equal to `c`

**Examples**:
- `Polynomial.coeff (X^2 + 3*X + 1) 1 = 3` ✓
- `Polynomial.coeff (C 5) 0 = 5` ✓
- `Polynomial.coeff (X + 1)^3 2 = 3` ✓

## 4. Purpose
Automatically proves equalities involving polynomial coefficients by evaluating the coefficient extraction and comparing with the expected value.

## 5. Input Types
- **Goal type**: `Polynomial.coeff p n = c` where `p : Polynomial R`, `n : ℕ`, `c : R`
- **Supported rings**: `ℕ, ℤ, ℚ, ZMod p, Fintype` instances with decidable equality
- **Polynomial forms**: Any expression that reduces to a `Polynomial R` term

## 6. Algorithm

1. **Goal Analysis**:
   - Parse goal to extract polynomial `p`, degree `n`, and expected coefficient `c`
   - Verify the goal matches the pattern `Polynomial.coeff _ _ = _`

2. **Normalization**:
   - Reduce degree expression `n` to concrete natural number using `norm_num`
   - Simplify polynomial `p` using `ring_nf` or polynomial normalization tactics

3. **Coefficient Extraction**:
   - Apply `Polynomial.coeff` evaluation lemmas
   - Use `simp` with polynomial coefficient simplification rules
   - Employ `norm_num` for arithmetic operations in the coefficient ring

4. **Verification**:
   - Check if the computed coefficient equals the expected value `c`
   - Apply reflexivity or use `norm_num` to prove the final equality

5. **Proof Construction**:
   - Build proof term using coefficient evaluation lemmas and definitional equality
   - Fall back to `simp` with appropriate polynomial lemmas if direct computation fails

## 7. Success Criteria

**Success conditions**:
- Goal matches the expected pattern
- Polynomial can be normalized to a form where coefficients are computable
- Degree reduces to a concrete natural number
- Coefficient computation yields a value definitionally equal to the expected result

**Failure conditions**:
- Goal is not a coefficient equality
- Polynomial involves non-computable elements
- Degree expression doesn't reduce to a concrete number
- Computed coefficient doesn't match expected value
- Coefficient ring lacks necessary decidability instances

## 8. Edge Cases

1. **Zero polynomial**: `Polynomial.coeff 0 n = 0` for any `n`
2. **Degree too high**: `Polynomial.coeff p n = 0` when `n > p.degree`
3. **Constant polynomial**: `Polynomial.coeff (C a) 0 = a`, `Polynomial.coeff (C a) n = 0` for `n > 0`
4. **Symbolic coefficients**: Handle cases where coefficients involve parameters
5. **Large degrees**: Optimize for polynomials with high degrees by using sparse representation
6. **Type class resolution**: Ensure proper instances for coefficient ring operations

## 9. Dependencies

```lean
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Simp
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fintype.Basic
```

**Key APIs needed**:
- `Polynomial.coeff` and related evaluation lemmas
- `norm_num` for numerical computation
- `ring_nf` for polynomial normalization
- Expression matching utilities from `Lean.Meta`
- Coefficient ring decidability instances

## Test Generation Algorithm

# Test Case Generation Algorithm for `poly_coeff` Tactic

## 1. Input Parameters

```lean
structure PolyCoeffTestParams where
  max_degree : Nat := 5           -- Maximum polynomial degree
  max_coeff_value : Nat := 10     -- Maximum absolute coefficient value
  num_tests_per_ring : Nat := 20  -- Number of tests per coefficient ring
  include_zero_cases : Bool := true
  include_symbolic : Bool := false -- Whether to include symbolic parameters
  rings : List RingType := [Nat, Int, Rat, ZMod2, ZMod3]
  
inductive RingType
  | Nat | Int | Rat | ZMod (n : Nat)
```

## 2. Core Algorithm

### Phase 1: Polynomial Structure Generation

**Step 1.1: Basic Polynomial Forms**
Generate polynomial templates using these building blocks:
- Constants: `C a` for coefficient values
- Variables: `X`, `X^n` 
- Sums: `p + q`
- Products: `p * q` (limited to keep degree manageable)
- Powers: `p^n` (small exponents only)

```lean
inductive PolyTemplate
  | const (a : Int)                    -- C a
  | var                                -- X  
  | pow (n : Nat)                      -- X^n
  | add (p q : PolyTemplate)           -- p + q
  | mul_const (a : Int) (p : PolyTemplate) -- a * p
  | compose (p : PolyTemplate) (n : Nat)   -- p^n (small n)
```

**Step 1.2: Degree-Bounded Generation**
Use recursive generation with degree tracking:

```lean
def generatePolys (maxDeg : Nat) : List PolyTemplate :=
  let rec go (deg : Nat) : List PolyTemplate :=
    if deg = 0 then [PolyTemplate.const (random_coeff)]
    else if deg = 1 then [var, add (const a) var] 
    else 
      -- Combine lower-degree polynomials
      let lower := go (deg - 1)
      let additions := do
        p ← lower
        q ← go (deg - degree p)  
        pure (add p q)
      additions ++ [pow deg] ++ (mul_const (random_coeff) <$> go deg)
  (List.range maxDeg).bind go
```

### Phase 2: Coefficient Query Generation

**Step 2.1: Systematic Degree Coverage**
For each polynomial `p` of degree `d`, generate queries for:
- `coeff p 0` (constant term)
- `coeff p d` (leading coefficient) 
- `coeff p k` for `k ∈ {1, 2, ..., d-1}` (intermediate terms)
- `coeff p (d+1), coeff p (d+2)` (beyond degree - should be 0)

**Step 2.2: Strategic Degree Selection**
```lean
def selectQueryDegrees (polyDeg : Nat) : List Nat :=
  [0] ++                           -- constant term
  (if polyDeg > 0 then [polyDeg] else []) ++  -- leading coefficient
  (List.range polyDeg).tail ++     -- intermediate coefficients  
  [polyDeg + 1, polyDeg + 2]       -- beyond polynomial degree
```

### Phase 3: Expected Value Computation

**Step 3.1: Symbolic Coefficient Calculation**
Use a symbolic polynomial evaluator to compute expected coefficients:

```lean
def computeExpectedCoeff (template : PolyTemplate) (degree : Nat) (ring : RingType) : Option (RingElement ring) :=
  match template with
  | const a => if degree = 0 then some (cast a) else some 0
  | var => if degree = 1 then some 1 else some 0  
  | pow n => if degree = n then some 1 else some 0
  | add p q => do
    cp ← computeExpectedCoeff p degree ring
    cq ← computeExpectedCoeff q degree ring  
    pure (cp + cq)
  | mul_const a p => do
    cp ← computeExpectedCoeff p degree ring
    pure (cast a * cp)
  | compose p n => computePowerCoeff p n degree ring
```

**Step 3.2: Multinomial Coefficient Handling**
For polynomial powers `(p)^n`, use binomial/multinomial theorem:

```lean  
def computePowerCoeff (p : PolyTemplate) (power degree : Nat) (ring : RingType) : Option (RingElement ring) :=
  -- For (a₀ + a₁X + ... + aₖXᵏ)^n, coefficient of Xᵈ is:
  -- ∑ over all ways to write d = i₁ + 2i₂ + ... + ki_k with i₁ + i₂ + ... + iₖ = n
  -- of (n choose i₁,i₂,...,iₖ) * a₀^i₁ * a₁^i₂ * ... * aₖ^iₖ
  computeMultinomialSum p power degree ring
```

### Phase 4: Test Case Filtering & Validation

**Step 4.1: Provability Criteria**
Only include test cases where:
1. The polynomial template can be converted to valid Lean syntax
2. All coefficients are computable in the target ring
3. The expected coefficient value is correct by manual verification
4. No intermediate steps require non-decidable operations

**Step 4.2: Redundancy Elimination**
Remove duplicate test cases up to:
- Ring isomorphism (e.g., `2 : ZMod 5` vs `7 : ZMod 5`)
- Polynomial equivalence (e.g., `X + 1` vs `1 + X`)  
- Trivial scaling (avoid too many `0 * p` cases)

## 3. Provability Criteria

A generated theorem `Polynomial.coeff p n = c` is provable by `poly_coeff` iff:

1. **Syntactic Criteria**:
   - `p` uses only `+`, `*`, `C`, `X`, `^` operations
   - `n` is a concrete natural number literal
   - `c` is a concrete element of the coefficient ring

2. **Semantic Criteria**:
   - `p` represents a well-defined polynomial over the coefficient ring
   - The coefficient ring has decidable equality and computable operations
   - Computing `coeff p n` terminates with a definite value

3. **Correctness Criteria**:
   - The expected value `c` equals the actual coefficient by symbolic computation
   - Intermediate normalization steps preserve polynomial equivalence

## 4. Complete Generation Algorithm

```lean
def generatePolyCoeffTests (params : PolyCoeffTestParams) : IO (List TestCase) := do
  let mut allTests := []
  
  for ring in params.rings do
    -- Phase 1: Generate polynomial templates  
    let polyTemplates := generatePolys params.max_degree
    
    for template in polyTemplates do
      let polyDegree := computeDegree template
      
      -- Phase 2: Generate degree queries
      let queryDegrees := selectQueryDegrees polyDegree
      
      for queryDeg in queryDegrees do
        -- Phase 3: Compute expected coefficient
        match computeExpectedCoeff template queryDeg ring with
        | some expectedCoeff =>
          -- Phase 4: Create and validate test case
          let testCase := {
            polynomial := templateToLeanExpr template ring,
            degree := queryDeg,
            expectedCoeff := expectedCoeff,
            ring := ring
          }
          if isProvableTestCase testCase then
            allTests := testCase :: allTests
        | none => continue
    
    -- Limit number of tests per ring
    allTests := allTests.take params.num_tests_per_ring
  
  pure allTests
```

## 5. Example Generated Test Cases

Here are 10 example theorem statements the algorithm would generate:

1. **Basic monomial** (Nat):
   ```lean
   example : Polynomial.coeff (X^3 : ℕ[X]) 3 = 1 := by poly_coeff
   ```

2. **Simple binomial** (Int):
   ```lean  
   example : Polynomial.coeff (X + C 5 : ℤ[X]) 0 = 5 := by poly_coeff
   ```

3. **Quadratic coefficient** (Rat):
   ```lean
   example : Polynomial.coeff (X^2 + 3*X + 7 : ℚ[X]) 1 = 3 := by poly_coeff
   ```

4. **Zero beyond degree** (ZMod 5):
   ```lean
   example : Polynomial.coeff (X^2 + 1 : (ZMod 5)[X]) 4 = 0 := by poly_coeff
   ```

5. **Constant polynomial** (Nat):
   ```lean
   example : Polynomial.coeff (C 42 : ℕ[X]) 0 = 42 := by poly_coeff
   ```

6. **Binomial expansion** (Int):
   ```lean
   example : Polynomial.coeff ((X + 1)^3 : ℤ[X]) 2 = 3 := by poly_coeff
   ```

7. **Leading coefficient** (ZMod 2):
   ```lean
   example : Polynomial.coeff (X^4 + X^3 + 1 : (ZMod 2)[X]) 4 = 1 := by poly_coeff
   ```

8. **Zero polynomial** (Rat):
   ```lean
   example : Polynomial.coeff (0 : ℚ[X]) 5 = 0 := by poly_coeff
   ```

9. **Mixed arithmetic** (Int):
   ```lean
   example : Polynomial.coeff (2*X^3 - 4*X + 1 : ℤ[X]) 3 = 2 := by poly_coeff
   ```

10. **Composed polynomial** (ZMod 3):
    ```lean
    example : Polynomial.coeff ((X^2 + 1)^2 : (ZMod 3)[X]) 2 = 2 := by poly_coeff
    ```

This algorithm provides systematic coverage of the tactic's capabilities while ensuring all generated test cases are provable and non-trivial.
