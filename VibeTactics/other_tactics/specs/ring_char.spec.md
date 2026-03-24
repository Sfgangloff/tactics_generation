> **User Request:** A tactic that extends the functionality of the `ring` tactic to handle ring characteristics specified by the `CharP` predicate. This tactic can solve ring equations by utilizing the fact that in a ring with characteristic n, adding an element to itself n times equals zero (i.e., n • x = 0). The tactic should work with both commutative rings (`CommRing`) and non-commutative rings (`Ring`). Examples include: proving `x + x + x + x = x` in a ring with characteristic 3 (since 4x = x + 3x = x + 0 = x), and proving `(x + y)^2 = x^2 + y^2` in a ring with characteristic 2 (since the cross terms 2xy = 0). The tactic should automatically recognize and utilize characteristic information to simplify ring expressions and prove equalities that depend on the ring's characteristic.

---

# Tactic Specification: ring_char

## Analysis

# Tactic Analysis: ring_char

## 1. Tactic Name
`ring_char`

## 2. Scope Analysis

### Most general interpretation
The broadest interpretation would handle arbitrary polynomial equations in rings with any characteristic, including:
- Non-linear polynomial identities of arbitrary degree
- Equations involving multiple variables and complex expressions
- Dynamic characteristic detection and reasoning
- Integration with arbitrary ring axioms and derived lemmas

### Lean constraints
- **Expression normalization**: Lean's ring tactic relies on computational normalization of polynomial expressions, which becomes complex with characteristic reasoning
- **Characteristic representation**: `CharP R n` requires `n` to be statically known at tactic execution time
- **Proof term construction**: Must construct valid proof terms using existing Mathlib lemmas about characteristics
- **Type class resolution**: Must work with Lean's type class system for ring structures

### Implementation complexity
A fully general approach would require:
- Custom polynomial normalization algorithms accounting for characteristic
- Complex case analysis on characteristic values
- Integration with existing ring tactic infrastructure
- Handling of non-decidable cases

### Chosen scope
Target **linear and quadratic polynomial equations** in rings with **statically determinable finite characteristic**. This balances:
- **Generality**: Covers the most common use cases (linear combinations, simple quadratic expansions)
- **Feasibility**: Leverages existing polynomial normalization with characteristic-specific simplification
- **User value**: Handles the examples given (characteristic 2 and 3 cases) effectively

## 3. Mathematical Specification

**Formula Class**: Goals of the form `e₁ = e₂` where:
- `e₁, e₂` are polynomial expressions over a ring `R` with `CharP R n` for some `n > 0`
- Each `eᵢ` is built from ring operations `(+, -, *, 0, 1)`, variables, and natural number scalar multiplication
- The degree in any single variable is ≤ 2

**Logical Fragment**: Equational first-order logic over ring signatures with characteristic predicates

**Provability Conditions**: A formula `e₁ = e₂` is provable if and only if:
- There exists a ring `R` with `CharP R n` in the context
- When both sides are expanded as polynomials and reduced modulo `n • x = 0` for all `x`, they are syntactically equal
- The equality can be proven using ring axioms plus the characteristic property `n • x = 0`

**Examples**:
- `4 • x = x` with `CharP R 3` (since `4 • x = (3 + 1) • x = 3 • x + x = 0 + x = x`)
- `(x + y)² = x² + y²` with `CharP R 2` (since `2 • (x * y) = 0`)

## 4. Purpose
Proves ring equations by utilizing characteristic properties to simplify expressions where scalar multiples become zero.

## 5. Input Types
- **Goal**: `e₁ = e₂` where `e₁, e₂ : R` for some ring type `R`
- **Context**: Must contain `CharP R n` instance for some `n : ℕ`
- **Ring Structure**: `[Ring R]` or `[CommRing R]` instance

## 6. Algorithm

1. **Characteristic Detection**: 
   - Search context for `CharP R n` instances
   - Extract the characteristic value `n`

2. **Expression Analysis**:
   - Parse both sides of the equality as polynomial expressions
   - Identify scalar multiples and expandable terms

3. **Characteristic Normalization**:
   - Apply distributivity to expand products
   - Collect like terms with scalar coefficients
   - Reduce coefficients modulo the characteristic `n`
   - Apply `n • x = 0` simplifications

4. **Fallback to Ring**:
   - If expressions normalize to identical forms, construct proof
   - Otherwise, attempt standard `ring` tactic as fallback

5. **Proof Construction**:
   - Build proof term using characteristic lemmas (`CharP.cast_eq_zero`, etc.)
   - Combine with ring axioms for the final equality

## 7. Success Criteria

**Success**: 
- Goal is an equality of ring expressions
- Characteristic `CharP R n` is available in context
- After characteristic-aware normalization, both sides are provably equal

**Failure**:
- Goal is not a ring equality
- No characteristic information available
- Expressions cannot be simplified to equality even with characteristic properties
- Expressions are too complex (degree > 2 or unsupported operations)

## 8. Edge Cases

1. **Characteristic 0**: Should delegate to standard `ring` tactic
2. **Multiple characteristics**: Error if conflicting `CharP` instances found
3. **Unknown characteristic**: Fail gracefully if characteristic is not a concrete natural number
4. **Non-polynomial expressions**: Handle division, inverses by failing gracefully
5. **Large characteristics**: May need optimization for characteristics with many digits
6. **Prime power characteristics**: Ensure correct handling of non-prime characteristics

## 9. Dependencies

```lean
import Mathlib.RingTheory.Characteristic.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.CommRing.Basic
import Mathlib.Tactic.NormNum
```

Key lemmas needed:
- `CharP.cast_eq_zero_iff`
- `CharP.add_pow_char_eq`  
- Ring distributivity and associativity lemmas
- Natural number arithmetic modulo characteristic

## Test Generation Algorithm

# Test Case Generation Algorithm for `ring_char` Tactic

## 1. Input Parameters

```lean
structure RingCharTestConfig where
  max_variables : ℕ := 3           -- Maximum number of ring variables
  max_degree : ℕ := 2              -- Maximum polynomial degree
  max_terms : ℕ := 6               -- Maximum terms per side
  characteristics : List ℕ := [2, 3, 5, 7]  -- Target characteristics to test
  include_zero_char : Bool := false -- Whether to include characteristic 0 cases
  max_coefficient : ℕ := 10        -- Maximum scalar coefficients
  complexity_levels : List ℕ := [1, 2, 3]  -- Complexity tiers
```

## 2. Core Algorithm

### Step 1: Expression Structure Generation

```lean
inductive RingExpr where
  | var : String → RingExpr                    -- Variable (x, y, z)
  | zero : RingExpr                           -- 0
  | one : RingExpr                            -- 1
  | add : RingExpr → RingExpr → RingExpr      -- e₁ + e₂
  | neg : RingExpr → RingExpr                 -- -e
  | mul : RingExpr → RingExpr → RingExpr      -- e₁ * e₂
  | smul : ℕ → RingExpr → RingExpr           -- n • e
```

**Expression Templates by Complexity:**

- **Level 1**: Linear combinations
  - `a • x + b • y`
  - `c • (x + y) + d • z`

- **Level 2**: Simple products and squares
  - `(x + y) * z`
  - `x^2 + y^2`
  - `(a • x + b • y)^2`

- **Level 3**: Mixed quadratic forms
  - `(x + y)^2 + (z + w)^2`
  - `a • x^2 + b • x * y + c • y^2`

### Step 2: Characteristic-Aware Normalization

For each characteristic `p` and expression `e`:

```lean
def normalize_mod_char (p : ℕ) (e : RingExpr) : RingExpr :=
  match e with
  | smul n x => smul (n % p) x
  | add e₁ e₂ => add (normalize_mod_char p e₁) (normalize_mod_char p e₂)
  | mul e₁ e₂ => 
    -- Apply characteristic-specific identities
    match p with
    | 2 => apply_char2_rules (mul (normalize_mod_char p e₁) (normalize_mod_char p e₂))
    | _ => mul (normalize_mod_char p e₁) (normalize_mod_char p e₂)
  | _ => e

def apply_char2_rules (e : RingExpr) : RingExpr :=
  -- (x + y)² = x² + y² in characteristic 2
  -- 2 • x = 0, so cross terms vanish
```

### Step 3: Provable Identity Generation

**Core Generation Strategy:**

1. **Start with a canonical form**: Generate a normalized polynomial
2. **Apply reverse transformations**: Create equivalent but different-looking expressions
3. **Verify provability**: Check that both sides normalize to the same form

```lean
def generate_identity (config : RingCharTestConfig) (char : ℕ) : 
  Option (RingExpr × RingExpr) :=
  -- Generate left side in canonical form
  let canonical := generate_canonical_expr config char
  -- Apply characteristic-preserving transformations
  let transformed := apply_char_transformations char canonical
  -- Verify they normalize to the same thing
  if normalize_mod_char char canonical = normalize_mod_char char transformed
  then some (canonical, transformed)
  else none
```

### Step 4: Characteristic-Specific Identity Patterns

**Characteristic 2 Patterns:**
- Binomial expansion: `(x + y)^n` vs `x^n + y^n` 
- Even coefficient elimination: `2k • x = 0`
- Additive inverse: `x = -x`

**Characteristic 3 Patterns:**
- Coefficient reduction: `4 • x = 1 • x`
- Triple terms: `3 • (expression) = 0`
- Cube identities: `(x + y)³` simplifications

**Characteristic p > 3 Patterns:**
- Modular arithmetic: `(p+k) • x = k • x`
- Fermat's little theorem applications
- Coefficient overflow: `ab • x` where `ab ≡ c (mod p)`

## 3. Provability Criteria

A generated identity `e₁ = e₂` is provable by `ring_char` if and only if:

1. **Syntactic Validity**: Both sides parse as valid ring expressions
2. **Degree Bounds**: Maximum degree ≤ 2 in any variable
3. **Characteristic Normalization**: `normalize_mod_char p e₁ = normalize_mod_char p e₂`
4. **Type Class Requirements**: Can synthesize `[Ring R]` and `[CharP R p]`

**Verification Algorithm:**
```lean
def is_provable (char : ℕ) (e₁ e₂ : RingExpr) : Bool :=
  let norm₁ := normalize_mod_char char e₁
  let norm₂ := normalize_mod_char char e₂
  syntactically_equal norm₁ norm₂
```

## 4. Complete Generation Algorithm

```lean
def generate_ring_char_tests (config : RingCharTestConfig) : List (ℕ × RingExpr × RingExpr) :=
  let results := []
  for char in config.characteristics do
    for complexity in config.complexity_levels do
      for _ in range (tests_per_level complexity) do
        match generate_by_template char complexity config with
        | some (lhs, rhs) => 
          if is_provable char lhs rhs 
          then results.append (char, lhs, rhs)
        | none => continue
  results

def generate_by_template (char : ℕ) (complexity : ℕ) (config : RingCharTestConfig) : 
  Option (RingExpr × RingExpr) :=
  match complexity with
  | 1 => generate_linear_identity char config
  | 2 => generate_quadratic_identity char config  
  | 3 => generate_mixed_identity char config
  | _ => none
```

## 5. Template-Specific Generators

### Linear Identity Generator
```lean
def generate_linear_identity (char : ℕ) (config : RingCharTestConfig) : Option (RingExpr × RingExpr) :=
  -- Pattern: Coefficient manipulation
  let vars := take config.max_variables ["x", "y", "z"]
  let coeffs := random_coeffs char config.max_coefficient
  let lhs := linear_combination coeffs vars
  let rhs := linear_combination (map (· % char) coeffs) vars
  some (lhs, rhs)
```

### Quadratic Identity Generator  
```lean
def generate_quadratic_identity (char : ℕ) (config : RingCharTestConfig) : Option (RingExpr × RingExpr) :=
  match char with
  | 2 => 
    -- (x + y)² = x² + y² pattern
    let x := var "x"
    let y := var "y" 
    let lhs := mul (add x y) (add x y)
    let rhs := add (mul x x) (mul y y)
    some (lhs, rhs)
  | p => 
    -- General coefficient reduction
    generate_coefficient_reduction_quadratic p config
```

## 6. Example Outputs

The algorithm would generate theorems like:

```lean
-- Characteristic 2 examples
theorem char2_test1 {R : Type*} [CommRing R] [CharP R 2] (x y : R) : 
  (x + y)^2 = x^2 + y^2 := by ring_char

theorem char2_test2 {R : Type*} [Ring R] [CharP R 2] (x : R) : 
  4 • x = 0 := by ring_char

theorem char2_test3 {R : Type*} [CommRing R] [CharP R 2] (x y z : R) : 
  2 • (x * y + z^2) = 0 := by ring_char

-- Characteristic 3 examples  
theorem char3_test1 {R : Type*} [Ring R] [CharP R 3] (x : R) : 
  7 • x = 1 • x := by ring_char

theorem char3_test2 {R : Type*} [CommRing R] [CharP R 3] (x y : R) : 
  (x + y)^3 = x^3 + y^3 := by ring_char

-- Characteristic 5 examples
theorem char5_test1 {R : Type*} [Ring R] [CharP R 5] (x y : R) : 
  8 • x + 3 • y = 3 • x + 3 • y := by ring_char

theorem char5_test2 {R : Type*} [CommRing R] [CharP R 5] (x : R) : 
  (2 • x)^2 = 4 • x^2 := by ring_char

-- Mixed complexity example
theorem char7_complex {R : Type*} [CommRing R] [CharP R 7] (x y z : R) : 
  9 • (x + y)^2 + 14 • z = 2 • (x^2 + 2•x•y + y^2) := by ring_char
```

## 7. Quality Assurance

**Diversity Metrics:**
- Variable count distribution
- Coefficient size distribution  
- Expression depth variance
- Characteristic coverage

**Correctness Verification:**
- All generated theorems must pass normalization check
- Cross-verify with known mathematical identities
- Stress test boundary cases (coefficient = characteristic)

This algorithm systematically explores the space of ring equations that become trivial under characteristic constraints, ensuring comprehensive test coverage for the `ring_char` tactic.
