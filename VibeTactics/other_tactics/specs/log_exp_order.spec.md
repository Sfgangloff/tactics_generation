> **User Request:** Tactic to decide the order on logarithmico-exponential functions. This tactic determines the ordering relationships between expressions involving logarithms, exponentials, and their compositions by applying known asymptotic growth rules and hierarchies of these functions.

---

# Tactic Specification: log_exp_order

## Analysis

# Tactic Analysis: Logarithmic-Exponential Order Decision

## 1. Tactic Name
`log_exp_order`

## 2. Scope Analysis

**Most general interpretation**: A complete decision procedure for all ordering relationships between arbitrary compositions of logarithms, exponentials, polynomials, and constants, handling multi-variable functions with complex nested structures like `log(exp(x^2 * log(y))) < exp(sqrt(x) * log(log(z)))`.

**Lean constraints**: 
- Expression matching in Lean 4 metaprogramming requires concrete syntactic patterns
- No built-in symbolic computation or limit evaluation
- Decidability requires finite, algorithmic procedures
- Real analysis in Mathlib has limited automation for asymptotic comparisons

**Implementation complexity**: A full decision procedure would require:
- Complex expression parsing and normalization
- Sophisticated asymptotic hierarchy encoding
- Multi-variable analysis with parameter relationships
- Integration with Mathlib's real analysis library

**Chosen scope**: Target univariate expressions built from a restricted grammar of well-understood functions, focusing on goals of the form `f x < g x` or `f x ≤ g x` where both sides are "eventually" comparable via standard asymptotic hierarchies. This balances mathematical usefulness with implementation feasibility.

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `∀ᶠ x in atTop, f x ⋄ g x` where:
- `⋄ ∈ {<, ≤, =}`  
- `f, g` are expressions built from the grammar:
  ```
  expr ::= ℝ | x | expr + expr | expr * expr | expr ^ ℝ | 
           Real.log expr | Real.exp expr | (expr)
  ```
- Both `f` and `g` are eventually positive and well-defined for large `x`

**Logical fragment**: First-order logic over real arithmetic with asymptotic quantification (∀ᶠ)

**Provability conditions**: A formula `∀ᶠ x in atTop, f x ⋄ g x` is provable when:
1. Both `f` and `g` can be assigned asymptotic growth rates from the hierarchy: `log^k x ≺ x^ε ≺ x^a ≺ exp x ≺ x^x ≺ exp(x^a) ≺ exp(exp x)` for `k ∈ ℕ`, `ε > 0`, `a > 0`
2. The relationship `⋄` holds between their assigned growth rates
3. No "oscillatory" or "incomparable" terms appear that would break the hierarchy

**Example**: `∀ᶠ x in atTop, x^2 * log x < exp x` is provable since `x^2 * log x` has growth rate `x^2` and `exp x` has growth rate `exp x`, with `x^a ≺ exp x`.

## 4. Purpose
Automatically proves or disproves asymptotic ordering relationships between univariate expressions involving logarithms, exponentials, polynomials, and their compositions.

## 5. Input Types
- Goals of type `∀ᶠ x in Filter.atTop, f x < g x` 
- Goals of type `∀ᶠ x in Filter.atTop, f x ≤ g x`
- Where `f g : ℝ → ℝ` are expressions in the supported grammar

## 6. Algorithm

1. **Parse and validate**: Extract `f` and `g` from the goal, verify they match the supported grammar
2. **Normalize expressions**: 
   - Expand products and collect like terms where possible
   - Handle standard simplifications (e.g., `exp(log x) = x`)
3. **Compute growth rates**:
   - Recursively assign each subexpression a position in the asymptotic hierarchy
   - Handle compositions using standard rules (e.g., `f(g(x))` where `g(x) → ∞`)
4. **Compare growth rates**: Apply the ordering from the asymptotic hierarchy
5. **Construct proof term**: Use appropriate Mathlib lemmas about `isLittleO`, `isBigO`, and `Filter.eventually` to build the proof

## 7. Success Criteria

**Success**: When both expressions can be assigned comparable positions in the asymptotic hierarchy and the relationship holds.

**Failure**: 
- Expressions contain unsupported functions
- Growth rates are incomparable (e.g., `sin x` vs `cos x`)
- Expressions are asymptotically equal but strict inequality is claimed
- Malformed expressions or type mismatches

## 8. Edge Cases

- **Equal growth rates**: `x^2` vs `2*x^2` → use `isBigO` instead of `isLittleO`
- **Negative expressions**: Reject or handle via absolute values with appropriate conditions
- **Constant functions**: Treat as growth rate `1` in the hierarchy
- **Nested logs/exps**: `log(log x)`, `exp(exp x)` → extend hierarchy appropriately
- **Fractional/negative exponents**: `x^(-1)`, `x^(1/2)` → place correctly in polynomial hierarchy

## 9. Dependencies

```lean
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.Order.LiminfLimsup
```

## Test Generation Algorithm

# Test Generation Algorithm for `log_exp_order` Tactic

## 1. Input Parameters

```lean
structure TestGenParams where
  max_nesting_depth : ℕ := 3        -- Maximum nesting of log/exp (e.g., log(log(x)))
  max_term_count : ℕ := 4           -- Maximum terms in sums/products
  exponent_range : List ℚ := [-2, -1, -1/2, 1/2, 1, 2, 3]  -- Allowed polynomial exponents
  constant_range : List ℕ := [1, 2, 3, 5, 10]  -- Multiplicative constants
  include_mixed : Bool := true       -- Include mixed operations (sum of different growth rates)
  relation_types : List Relation := [LT, LE]    -- Types of comparisons to generate
```

## 2. Expression Grammar and Generation

### 2.1 Abstract Syntax Tree
```lean
inductive ExprAST where
  | const : ℚ → ExprAST                    -- Positive constants
  | var : ExprAST                          -- Variable x
  | add : ExprAST → ExprAST → ExprAST      -- Addition
  | mul : ExprAST → ExprAST → ExprAST      -- Multiplication  
  | pow : ExprAST → ℚ → ExprAST           -- Exponentiation x^r
  | log : ExprAST → ExprAST               -- Logarithm
  | exp : ExprAST → ExprAST               -- Exponential
```

### 2.2 Growth Rate Classification
```lean
inductive GrowthRate where
  | constant : ℚ → GrowthRate                           -- O(1)
  | poly_neg : ℚ → GrowthRate                          -- O(x^(-a)), a > 0
  | log_power : ℕ → GrowthRate                         -- O(log^k x)
  | poly_pos : ℚ → GrowthRate                          -- O(x^a), a > 0
  | exp_poly : ℚ → GrowthRate                          -- O(exp(x^a)), a > 0
  | double_exp : GrowthRate                            -- O(exp(exp(x)))
  | mixed : List GrowthRate → GrowthRate               -- Sums of different rates
```

## 3. Core Test Generation Algorithm

### 3.1 Expression Generation by Growth Rate

```lean
def generateByGrowthRate (rate : GrowthRate) (params : TestGenParams) : List ExprAST :=
  match rate with
  | GrowthRate.constant c => 
    [ExprAST.const c]
    
  | GrowthRate.poly_neg a => 
    params.constant_range.map (fun k => 
      ExprAST.mul (ExprAST.const k) (ExprAST.pow ExprAST.var (-a)))
    
  | GrowthRate.log_power k => 
    let base_logs := iterateLog ExprAST.var k  -- log^k(x)
    params.constant_range.map (fun c => ExprAST.mul (ExprAST.const c) base_logs)
    
  | GrowthRate.poly_pos a => 
    params.constant_range.flatMap (fun k =>
      [ExprAST.mul (ExprAST.const k) (ExprAST.pow ExprAST.var a),
       ExprAST.mul (ExprAST.pow ExprAST.var a) (ExprAST.log ExprAST.var)])  -- x^a * log(x)
    
  | GrowthRate.exp_poly a => 
    [ExprAST.exp (ExprAST.pow ExprAST.var a),
     ExprAST.mul (ExprAST.const 2) (ExprAST.exp (ExprAST.pow ExprAST.var a))]
     
  | GrowthRate.double_exp => 
    [ExprAST.exp (ExprAST.exp ExprAST.var)]
    
  | GrowthRate.mixed rates => 
    generateMixedExpressions rates params

def iterateLog (expr : ExprAST) (k : ℕ) : ExprAST :=
  match k with
  | 0 => ExprAST.const 1
  | 1 => ExprAST.log expr  
  | n+1 => ExprAST.log (iterateLog expr n)
```

### 3.2 Provable Pair Generation

```lean
-- Growth rate hierarchy (strict ordering)
def growthOrdering : List GrowthRate := [
  GrowthRate.constant 1,
  GrowthRate.poly_neg (1/2), GrowthRate.poly_neg 1, GrowthRate.poly_neg 2,
  GrowthRate.log_power 1, GrowthRate.log_power 2, GrowthRate.log_power 3,
  GrowthRate.poly_pos (1/2), GrowthRate.poly_pos 1, GrowthRate.poly_pos 2, 
  GrowthRate.poly_pos 3,
  GrowthRate.exp_poly 1,
  GrowthRate.exp_poly 2,
  GrowthRate.double_exp
]

def generateProvablePairs (params : TestGenParams) : List (ExprAST × ExprAST × Relation) :=
  let rates := growthOrdering
  let pairs := []
  
  -- Generate strict inequality pairs (f < g where f grows slower than g)
  for i in [0 : rates.length] do
    for j in [i+1 : rates.length] do
      let slower_rate := rates[i]!
      let faster_rate := rates[j]!
      let slower_exprs := generateByGrowthRate slower_rate params
      let faster_exprs := generateByGrowthRate faster_rate params
      
      for f in slower_exprs do
        for g in faster_exprs do
          pairs := pairs ++ [(f, g, Relation.LT), (f, g, Relation.LE)]
  
  -- Generate equal growth rate pairs (f ≤ g where f, g have same growth rate)  
  for rate in rates do
    let exprs := generateByGrowthRate rate params
    for f in exprs do
      for g in exprs do
        if f ≠ g then pairs := pairs ++ [(f, g, Relation.LE)]
  
  pairs
```

### 3.3 Expression Complexity Control

```lean
def controlComplexity (expr : ExprAST) (max_depth : ℕ) : Bool :=
  nestingDepth expr ≤ max_depth ∧ termCount expr ≤ max_term_count
  
def nestingDepth : ExprAST → ℕ
  | ExprAST.const _ => 0
  | ExprAST.var => 0  
  | ExprAST.add e1 e2 => max (nestingDepth e1) (nestingDepth e2)
  | ExprAST.mul e1 e2 => max (nestingDepth e1) (nestingDepth e2)
  | ExprAST.pow e _ => nestingDepth e
  | ExprAST.log e => 1 + nestingDepth e
  | ExprAST.exp e => 1 + nestingDepth e

def termCount : ExprAST → ℕ  
  | ExprAST.add e1 e2 => termCount e1 + termCount e2
  | ExprAST.mul e1 e2 => max (termCount e1) (termCount e2)  -- Products don't increase term count
  | _ => 1
```

## 4. Provability Criteria

### 4.1 Asymptotic Relationship Rules

```lean
-- Check if f ⋄ g is provable based on growth rates
def isProvable (f g : ExprAST) (rel : Relation) : Bool :=
  let rate_f := computeGrowthRate f
  let rate_g := computeGrowthRate g
  
  match rel with
  | Relation.LT => strictlySlower rate_f rate_g
  | Relation.LE => strictlySlower rate_f rate_g ∨ sameGrowthRate rate_f rate_g
  | Relation.EQ => sameGrowthRate rate_f rate_g

def strictlySlower (r1 r2 : GrowthRate) : Bool :=
  growthOrdering.indexOf r1 < growthOrdering.indexOf r2

def sameGrowthRate (r1 r2 : GrowthRate) : Bool :=
  growthClass r1 = growthClass r2  -- Same position in hierarchy
```

### 4.2 Expression Validity

```lean
def isValidExpression (expr : ExprAST) : Bool :=
  eventuallyPositive expr ∧ wellDefined expr
  
def eventuallyPositive : ExprAST → Bool
  | ExprAST.const c => c > 0
  | ExprAST.var => true
  | ExprAST.add e1 e2 => eventuallyPositive e1 ∧ eventuallyPositive e2
  | ExprAST.mul e1 e2 => eventuallyPositive e1 ∧ eventuallyPositive e2
  | ExprAST.pow e r => eventuallyPositive e ∧ (r > 0 ∨ growsFaster e (ExprAST.const 1))
  | ExprAST.log e => growsFaster e (ExprAST.const 1)  -- Need e > 1 eventually
  | ExprAST.exp e => true
```

## 5. Complete Test Generation Procedure

```lean
def generateTestSuite (params : TestGenParams) : List String :=
  let provable_pairs := generateProvablePairs params
  let filtered_pairs := provable_pairs.filter (fun (f, g, rel) =>
    controlComplexity f params.max_nesting_depth ∧
    controlComplexity g params.max_nesting_depth ∧
    isValidExpression f ∧ 
    isValidExpression g ∧
    isProvable f g rel)
  
  filtered_pairs.map formatAsLeanTheorem

def formatAsLeanTheorem (f g : ExprAST) (rel : Relation) : String :=
  let f_lean := exprToLean f
  let g_lean := exprToLean g  
  let rel_sym := relationSymbol rel
  s!"theorem test_log_exp_order_{hash (f,g,rel)} : " ++
  s!"∀ᶠ x in Filter.atTop, {f_lean} {rel_sym} {g_lean} := by log_exp_order"
```

## 6. Example Generated Theorems

The algorithm would generate theorems like:

1. **Basic polynomial vs exponential:**
```lean
theorem test_log_exp_order_001 : 
  ∀ᶠ x in Filter.atTop, x^2 < Real.exp x := by log_exp_order
```

2. **Logarithmic vs polynomial:**
```lean
theorem test_log_exp_order_002 : 
  ∀ᶠ x in Filter.atTop, Real.log x ^ 3 < x^(1/2) := by log_exp_order
```

3. **Mixed terms with same growth rate:**
```lean
theorem test_log_exp_order_003 : 
  ∀ᶠ x in Filter.atTop, x^2 * Real.log x ≤ 5 * x^2 := by log_exp_order
```

4. **Nested exponentials:**
```lean
theorem test_log_exp_order_004 : 
  ∀ᶠ x in Filter.atTop, Real.exp x < Real.exp (Real.exp x) := by log_exp_order
```

5. **Composite expressions:**
```lean
theorem test_log_exp_order_005 : 
  ∀ᶠ x in Filter.atTop, x^3 + Real.log x < Real.exp (x^2) := by log_exp_order
```

6. **Negative exponents:**
```lean
theorem test_log_exp_order_006 : 
  ∀ᶠ x in Filter.atTop, x^(-1) < Real.log x := by log_exp_order
```

7. **Nested logarithms:**
```lean
theorem test_log_exp_order_007 : 
  ∀ᶠ x in Filter.atTop, Real.log (Real.log x) < Real.log x := by log_exp_order
```

8. **Complex composition:**
```lean
theorem test_log_exp_order_008 : 
  ∀ᶠ x in Filter.atTop, Real.log x * x^(1/2) < x * Real.log x := by log_exp_order
```

9. **Multiple terms:**
```lean
theorem test_log_exp_order_009 : 
  ∀ᶠ x in Filter.atTop, 2*x^2 + 3*x + Real.log x ≤ x^3 := by log_exp_order
```

10. **Equal growth rates:**
```lean
theorem test_log_exp_order_010 : 
  ∀ᶠ x in Filter.atTop, x^2 ≤ x^2 + x := by log_exp_order
```

This systematic approach ensures comprehensive coverage of the tactic's intended scope while maintaining provability guarantees through the asymptotic growth rate hierarchy.
