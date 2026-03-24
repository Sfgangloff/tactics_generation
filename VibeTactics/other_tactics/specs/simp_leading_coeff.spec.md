> **User Request:** Tactic that computes the leading coefficient of a polynomial expression. Can simplify expressions of the form `leadingCoeff p` where `p` is a polynomial, reducing them to their numerical value.

---

# Tactic Specification: simp_leading_coeff

## Analysis

# Tactic Analysis: Leading Coefficient Computation

## 1. Tactic Name
`simp_leading_coeff`

## 2. Scope Analysis

**Most general interpretation**: A tactic that could handle any goal involving `leadingCoeff` applied to arbitrary polynomial expressions, potentially involving complex polynomial operations, compositions, and abstract polynomial types across any commutative semiring.

**Lean constraints**: 
- Limited to polynomial expressions that can be structurally analyzed at the meta level
- Requires decidable coefficient extraction from concrete polynomial representations
- Expression matching capabilities are bounded by Lean's expression API
- Cannot handle polynomials defined through arbitrary functions or non-constructive definitions

**Implementation complexity**: 
- Full generality would require sophisticated polynomial normalization and symbolic computation
- Complex polynomial operations (multiplication, composition) would require significant algebraic machinery
- Abstract polynomial types would need extensive API integration

**Chosen scope**: Target goals of the form `leadingCoeff p = c` where `p` is a concrete polynomial expression built from:
- Polynomial variables (`X`, `Polynomial.X`)
- Coefficient scalars (numerals, variables of coefficient type)
- Basic operations (`+`, `*`, `Polynomial.monomial`, `Polynomial.C`)
- Simple polynomial constructors

This scope balances practical utility with implementable complexity while covering the most common use cases for leading coefficient simplification.

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `leadingCoeff p = c` where:
- `p` is a polynomial expression over a commutative semiring `R`
- `c` is an expression of type `R`
- `p` is built from constructors: `Polynomial.X`, `Polynomial.C`, `(+)`, `(*)`, `Polynomial.monomial`

**Logical fragment**: First-order equality statements over polynomial algebra structures

**Provability conditions**: A formula `leadingCoeff p = c` has a proof when:
- `p` can be reduced to a standard form `Σᵢ aᵢ * X^i` where the `aᵢ` are concrete coefficients
- The highest degree term has coefficient that simplifies to `c`
- The simplification is provable using Mathlib's polynomial lemmas and ring/field arithmetic

**Example formulas**:
- `leadingCoeff (3 * X^2 + 2 * X + 1) = 3`
- `leadingCoeff (X^3 + X) = 1`
- `leadingCoeff (Polynomial.C a * X^2 + b) = a` (when `a ≠ 0`)

## 4. Purpose
Automatically simplifies goals involving `leadingCoeff` by computing the leading coefficient of concrete polynomial expressions.

## 5. Input Types
- **Goal type**: `leadingCoeff p = c` where `p : Polynomial R` and `c : R` for some commutative semiring `R`
- **Alternative**: Goals where `leadingCoeff p` appears in larger expressions that can be simplified

## 6. Algorithm

1. **Pattern matching**: Check if goal has form `leadingCoeff p = c` or contains `leadingCoeff p` subexpressions
2. **Polynomial parsing**: Recursively analyze polynomial expression `p`:
   - Extract monomials and their coefficients
   - Handle `Polynomial.C`, `Polynomial.X`, `Polynomial.monomial` constructors
   - Process addition and multiplication operations
3. **Degree computation**: Determine the highest degree terms in the polynomial
4. **Coefficient extraction**: Extract the coefficient of the highest degree term
5. **Simplification**: Apply ring/field simplification to reduce the coefficient expression
6. **Proof construction**: Build proof term using:
   - `Polynomial.leadingCoeff_add`, `Polynomial.leadingCoeff_mul`
   - `Polynomial.leadingCoeff_C`, `Polynomial.leadingCoeff_X`
   - Ring/field arithmetic lemmas for coefficient simplification

## 7. Success Criteria

**Success conditions**:
- Polynomial expression consists only of supported constructors
- Leading coefficient can be computed symbolically
- Required polynomial and ring lemmas are available
- Coefficient simplification terminates

**Failure conditions**:
- Abstract or non-concrete polynomial expressions
- Polynomials involving unsupported operations (e.g., composition, evaluation)
- Coefficient expressions that don't simplify
- Missing instances for the coefficient type

## 8. Edge Cases

1. **Zero polynomial**: `leadingCoeff 0 = 0` (handle via `Polynomial.leadingCoeff_zero`)
2. **Constant polynomial**: `leadingCoeff (Polynomial.C a) = a` when `a ≠ 0`, otherwise `0`
3. **Polynomial with symbolic coefficients**: May require additional assumptions about non-zero coefficients
4. **Nested polynomial expressions**: Limited to expressions that can be flattened structurally
5. **Different coefficient types**: Handle coercions between `ℕ`, `ℤ`, `ℚ`, `ℝ`, etc.

## 9. Dependencies

```lean
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Simp
```

**Key lemmas needed**:
- `Polynomial.leadingCoeff_add`
- `Polynomial.leadingCoeff_mul` 
- `Polynomial.leadingCoeff_C`
- `Polynomial.leadingCoeff_X`
- `Polynomial.leadingCoeff_monomial`
- Ring arithmetic simplification lemmas

## Test Generation Algorithm

# Test Case Generation Algorithm for `simp_leading_coeff`

## 1. Input Parameters

```lean
structure TestGenParams where
  max_degree : ℕ := 4          -- Maximum polynomial degree
  max_terms : ℕ := 5           -- Maximum number of terms in polynomial
  max_coeff_size : ℕ := 10     -- Maximum absolute value of numeric coefficients
  coeff_types : List String := ["ℕ", "ℤ", "ℚ", "ℝ"]  -- Coefficient ring types
  include_symbolic : Bool := true   -- Include symbolic coefficients (a, b, c)
  include_zero_cases : Bool := true -- Include edge cases with zero
  nesting_depth : ℕ := 2       -- Max depth of nested operations
  num_tests_per_structure : ℕ := 3  -- Tests per polynomial structure type
```

## 2. Core Algorithm

### Phase 1: Polynomial Structure Enumeration

```lean
inductive PolyStructure where
  | constant : ℕ → PolyStructure  -- Polynomial.C coefficient
  | variable : PolyStructure      -- X
  | monomial : ℕ → ℕ → PolyStructure  -- coeff * X^degree
  | add : PolyStructure → PolyStructure → PolyStructure
  | mul : PolyStructure → PolyStructure → PolyStructure
  | scale : ℕ → PolyStructure → PolyStructure  -- coefficient * polynomial
```

**Algorithm Step 1: Generate Base Structures**
```
function generate_base_structures(max_degree: ℕ, max_terms: ℕ) -> List[PolyStructure]:
  structures = []
  
  -- Single term polynomials
  for d in 0..max_degree:
    structures.append(monomial(1, d))  -- X^d
    if d > 0:
      structures.append(monomial(coeff_var(), d))  -- c * X^d
  
  -- Multi-term polynomials via addition
  for num_terms in 2..max_terms:
    for degree_partition in partitions(max_degree, num_terms):
      poly = monomial(coeff_var(), degree_partition[0])
      for i in 1..num_terms-1:
        poly = add(poly, monomial(coeff_var(), degree_partition[i]))
      structures.append(poly)
  
  return structures
```

### Phase 2: Coefficient Assignment

**Algorithm Step 2: Generate Coefficient Contexts**
```
inductive CoeffContext where
  | numeric : ℤ → CoeffContext     -- Concrete numbers
  | symbolic : String → CoeffContext  -- Variables a, b, c
  | mixed : List[CoeffContext] → CoeffContext

function generate_coeff_contexts(params: TestGenParams) -> List[CoeffContext]:
  contexts = []
  
  -- Pure numeric contexts
  for i in 1..params.max_coeff_size:
    contexts.append(numeric(i))
    contexts.append(numeric(-i))
  
  -- Pure symbolic contexts  
  contexts.append(symbolic("a"))
  contexts.append(mixed([symbolic("a"), symbolic("b")]))
  contexts.append(mixed([symbolic("a"), symbolic("b"), symbolic("c")]))
  
  -- Mixed numeric-symbolic
  contexts.append(mixed([numeric(2), symbolic("a")]))
  contexts.append(mixed([symbolic("a"), numeric(1), symbolic("b")]))
  
  return contexts
```

### Phase 3: Leading Coefficient Computation

**Algorithm Step 3: Compute Expected Leading Coefficient**
```
function compute_leading_coeff(poly: PolyStructure, context: CoeffContext) -> (ℕ, CoeffExpr):
  match poly:
    | constant(c) => (0, context.lookup(c))
    | variable => (1, "1")
    | monomial(c, d) => (d, context.lookup(c))
    | add(p1, p2) => 
        let (d1, c1) = compute_leading_coeff(p1, context)
        let (d2, c2) = compute_leading_coeff(p2, context)
        if d1 > d2: (d1, c1)
        else if d2 > d1: (d2, c2)
        else: (d1, simplify_add(c1, c2))
    | mul(p1, p2) =>
        let (d1, c1) = compute_leading_coeff(p1, context)
        let (d2, c2) = compute_leading_coeff(p2, context)
        (d1 + d2, simplify_mul(c1, c2))
    | scale(c, p) =>
        let (d, coeff) = compute_leading_coeff(p, context)
        (d, simplify_mul(context.lookup(c), coeff))
```

### Phase 4: Provability Filtering

**Algorithm Step 4: Ensure Provability**
```
function is_provable(poly: PolyStructure, expected_coeff: CoeffExpr, ring_type: String) -> Bool:
  -- Check if polynomial is in supported fragment
  if not is_supported_structure(poly): return false
  
  -- Check if coefficient computation is decidable
  if not is_decidable_coeff(expected_coeff, ring_type): return false
  
  -- Check for edge cases that need special handling
  if involves_zero_division(expected_coeff): return false
  if requires_nonzero_assumptions(expected_coeff) and not has_assumptions(): return false
  
  -- Verify simplification terminates
  if not simplification_terminates(expected_coeff): return false
  
  return true

function is_supported_structure(poly: PolyStructure) -> Bool:
  -- Recursively check if all operations are supported
  match poly:
    | constant(_) | variable | monomial(_, _) => true
    | add(p1, p2) | mul(p1, p2) => 
        is_supported_structure(p1) and is_supported_structure(p2)
    | scale(_, p) => is_supported_structure(p)
    | _ => false  -- Unsupported operations
```

### Phase 5: Test Case Generation

**Algorithm Step 5: Generate Final Test Cases**
```
function generate_test_cases(params: TestGenParams) -> List[TestCase]:
  test_cases = []
  
  for ring_type in params.coeff_types:
    for structure in generate_base_structures(params.max_degree, params.max_terms):
      for context in generate_coeff_contexts(params):
        let (degree, expected_coeff) = compute_leading_coeff(structure, context)
        
        if is_provable(structure, expected_coeff, ring_type):
          let poly_expr = render_polynomial(structure, context, ring_type)
          let coeff_expr = render_coefficient(expected_coeff, ring_type)
          
          test_cases.append(TestCase {
            statement: f"leadingCoeff ({poly_expr}) = {coeff_expr}",
            ring_type: ring_type,
            complexity: compute_complexity(structure),
            category: classify_test(structure, context)
          })
  
  return filter_and_balance(test_cases, params)
```

## 3. Provability Criteria

A generated theorem `leadingCoeff p = c` is provable if:

1. **Structural Requirements**:
   - `p` uses only supported constructors (`C`, `X`, `monomial`, `+`, `*`)
   - No abstract polynomial operations (composition, evaluation, etc.)
   - Finite depth of nested operations

2. **Coefficient Requirements**:
   - All coefficients are concrete numerals or declared variables
   - No division by expressions that might be zero
   - Ring operations terminate under simplification

3. **Degree Requirements**:
   - Leading degree is well-defined and finite
   - No degree overflow in computations

4. **Type Requirements**:
   - Target ring has necessary instances (CommSemiring, etc.)
   - Coercions between coefficient types are available

## 4. Example Outputs

The algorithm would generate test cases like:

### Basic Polynomial Tests
```lean
example : leadingCoeff (X^3 + 2*X + 1 : ℤ[X]) = 1 := by simp_leading_coeff

example : leadingCoeff (3*X^2 + X + 5 : ℚ[X]) = 3 := by simp_leading_coeff

example : leadingCoeff (X^4 + X^2 : ℕ[X]) = 1 := by simp_leading_coeff
```

### Symbolic Coefficient Tests
```lean
example (a b : ℝ) : leadingCoeff (a*X^2 + b*X + 1 : ℝ[X]) = a := by simp_leading_coeff

example (c : ℤ) : leadingCoeff (c*X^3 + X + 2 : ℤ[X]) = c := by simp_leading_coeff
```

### Monomial Constructor Tests  
```lean
example : leadingCoeff (Polynomial.monomial 3 5 + Polynomial.monomial 1 2 : ℕ[X]) = 5 := by simp_leading_coeff

example : leadingCoeff (Polynomial.C 7 * X^2 + Polynomial.C 3 : ℚ[X]) = 7 := by simp_leading_coeff
```

### Edge Cases
```lean
example : leadingCoeff (0 : ℝ[X]) = 0 := by simp_leading_coeff

example : leadingCoeff (Polynomial.C 42 : ℤ[X]) = 42 := by simp_leading_coeff

example (a : ℚ) : leadingCoeff (X + a : ℚ[X]) = 1 := by simp_leading_coeff
```

### Multiplication Tests
```lean
example : leadingCoeff ((X + 1) * (X^2 + 2) : ℤ[X]) = 1 := by simp_leading_coeff

example (a : ℝ) : leadingCoeff (a * X * (X^2 + 1) : ℝ[X]) = a := by simp_leading_coeff
```

### Complex Expression Tests
```lean
example : leadingCoeff (X^3 + 2*X^3 + X + 1 : ℕ[X]) = 3 := by simp_leading_coeff

example (a b : ℚ) : leadingCoeff ((a*X + b) * (X^2 + 1) : ℚ[X]) = a := by simp_leading_coeff
```

This algorithm systematically explores the space of polynomial expressions that `simp_leading_coeff` should handle, ensuring comprehensive test coverage while maintaining provability guarantees.
