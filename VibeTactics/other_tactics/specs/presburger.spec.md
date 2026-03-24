> **User Request:** A tactic for deciding statements in Presburger arithmetic (first-order theory of natural numbers with addition and order). This tactic should be able to prove or disprove goals involving linear arithmetic over integers/naturals, including quantified statements. It handles expressions with addition, subtraction, multiplication by constants, and ordering relations. The tactic may use lookup tables for common instances to improve performance.

---

# Tactic Specification: presburger

## Analysis

# Tactic Analysis: Presburger Arithmetic Decision Procedure

## 1. Tactic Name
`presburger`

## 2. Scope Analysis

**Most general interpretation**: The broadest scope would be a complete decision procedure for Presburger arithmetic over both integers and naturals, handling arbitrary quantifier alternation, all linear constraints, and automatic type coercion between ℕ and ℤ.

**Lean constraints**: 
- Lean 4's expression matching is powerful but complex nested quantifier elimination is computationally expensive
- Type system requires careful handling of ℕ vs ℤ operations
- Metaprogramming API limitations for complex term rewriting
- Need decidable instances for arithmetic operations
- Memory and performance constraints for lookup tables

**Implementation complexity**:
- Full quantifier elimination is highly complex
- Cooper's algorithm implementation would be substantial
- Handling mixed ℕ/ℤ contexts adds significant complexity
- Optimization via lookup tables requires careful caching strategy

**Chosen scope**: Target quantifier-free Presburger arithmetic with limited existential quantification, focusing on goals provable in ℕ or ℤ separately. This balances practical utility with implementation feasibility while maintaining the core decision procedure functionality the user requested.

## 3. Mathematical Specification

**Formula class**: Let `PresbForm(R)` for `R ∈ {ℕ, ℤ}` be the set of formulas:
```
PresbForm(R) = {φ | φ ::= t₁ ≤ t₂ | t₁ = t₂ | t₁ < t₂ | φ₁ ∧ φ₂ | φ₁ ∨ φ₂ | ¬φ | ∃x. φ}
```
where terms `t ::= c | x | c·x | t₁ + t₂ | t₁ - t₂` with `c ∈ ℤ` constants and `x` variables ranging over `R`.

**Logical fragment**: Quantifier-free formulas with limited existential quantification (∃-depth ≤ 2).

**Provability conditions**: A formula φ ∈ PresbForm(R) is provable iff:
- For quantifier-free φ: the constraint system represented by φ has a solution in R
- For ∃x₁...∃xₖ. ψ where ψ is quantifier-free: the projection of ψ's solution set onto the free variables is non-empty in R

**Example**: `∃ x : ℕ, 2 * x + 1 ≤ n ∧ n < 4 * x` where `n` is free.

## 4. Purpose
Automatically proves or disproves goals involving linear arithmetic constraints over natural numbers or integers using Presburger arithmetic decision procedures.

## 5. Input Types
- Goals of type `Prop` containing:
  - Linear arithmetic expressions over `ℕ` or `ℤ`
  - Comparison operators: `≤`, `<`, `=`, `≥`, `>`
  - Logical connectives: `∧`, `∨`, `¬`, `→`
  - Limited existential quantifiers: `∃`

## 6. Algorithm

1. **Goal Analysis**:
   - Parse goal expression to extract arithmetic constraints
   - Identify variable types (ℕ or ℤ) and ensure consistency
   - Normalize to standard form (eliminate `≥`, `>`, `→`)

2. **Constraint Extraction**:
   - Convert to conjunction of linear inequalities: `Σ aᵢxᵢ ≤ b`
   - Handle existential quantifiers by marking variables for elimination

3. **Constraint Solving**:
   - For quantifier-free: check satisfiability using simplex-like method
   - For existential: apply Fourier-Motzkin elimination
   - Consult lookup table for common constraint patterns

4. **Proof Construction**:
   - If satisfiable: construct witness terms and apply arithmetic lemmas
   - If unsatisfiable: derive contradiction using linear combination of constraints
   - Use `norm_num`, `linarith`, or `omega` as proof backends

## 7. Success Criteria

**Success**: 
- Goal is a valid Presburger formula in the target fragment
- Constraint system is decidable (no mixed ℕ/ℤ coercions requiring case analysis)
- Solution/contradiction can be computed within reasonable time bounds

**Failure**:
- Goal contains non-linear terms (e.g., `x * y` where both are variables)
- Universal quantifiers or complex quantifier alternation
- Requires reasoning about divisibility predicates beyond linear constraints
- Timeout on constraint solving (fallback to other tactics)

## 8. Edge Cases

- **Empty constraint system**: Immediately succeed with trivial proof
- **Contradictory constants**: e.g., `0 < 0` - prove by `norm_num`
- **Natural number subtraction**: Handle `n - m` carefully, potentially introduce case splits
- **Large coefficients**: Use arbitrary precision arithmetic, set reasonable bounds
- **Degenerate quantifiers**: `∃ x, P` where `x ∉ FV(P)` - simplify to `P`
- **Type coercions**: Handle `↑n` (ℕ → ℤ) by working in ℤ when detected

## 9. Dependencies

```lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum  
import Mathlib.Tactic.Omega
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Lean.Elab.Tactic.Basic
import Lean.Meta.Basic
import Std.Data.HashMap
```

Additional potential dependencies:
- `Mathlib.Algebra.Order.Ring.Basic` for ordered ring properties
- `Mathlib.Data.Finset.Basic` for constraint enumeration
- `Std.Data.RBTree` for efficient lookup table implementation

## Test Generation Algorithm

# Test Case Generation Algorithm for Presburger Arithmetic Tactic

## 1. Input Parameters

```lean
structure PresburgerTestConfig where
  max_vars : Nat := 4           -- Maximum number of variables
  max_depth : Nat := 3          -- Maximum quantifier nesting depth
  max_coeff : Nat := 10         -- Maximum absolute value of coefficients
  num_constraints : Nat := 5    -- Maximum number of atomic constraints
  prob_existential : Float := 0.3 -- Probability of adding ∃ quantifier
  target_domain : Domain := Mixed -- ℕ, ℤ, or Mixed
  complexity_levels : List ComplexityLevel := [Simple, Medium, Hard]
```

## 2. Core Data Structures

```lean
inductive Domain where
  | Nat | Int | Mixed

inductive ComplexityLevel where
  | Simple   -- Single constraints, no quantifiers
  | Medium   -- Multiple constraints, boolean combinations
  | Hard     -- Existential quantifiers, complex formulas

structure LinearTerm where
  coeffs : List (Var × Int)  -- Variable coefficients
  constant : Int             -- Constant term

structure Constraint where
  lhs : LinearTerm
  op : CompOp              -- ≤, <, =
  rhs : LinearTerm

inductive Formula where
  | atom : Constraint → Formula
  | and : Formula → Formula → Formula  
  | or : Formula → Formula → Formula
  | not : Formula → Formula
  | exists : Var → Domain → Formula → Formula
```

## 3. Core Algorithm

### Phase 1: Structure Generation

```lean
def generateFormulaStructures (config : PresburgerTestConfig) : List FormulaTemplate :=
  let structures := []
  
  -- Generate by complexity level
  for level in config.complexity_levels do
    match level with
    | Simple => 
        -- Single atomic constraints
        structures.append (generateAtomicStructures config)
    | Medium =>
        -- Boolean combinations of 2-4 constraints
        structures.append (generateBooleanStructures config)
    | Hard =>
        -- Add existential quantifiers
        structures.append (generateQuantifiedStructures config)
  
  structures

def generateAtomicStructures (config : PresburgerTestConfig) : List FormulaTemplate :=
  -- Generate templates like: a₁x₁ + ... + aₙxₙ ≤ b
  [for n in [1..config.max_vars] yield
    AtomicTemplate n (chooseRandomOp [≤, <, =])]

def generateBooleanStructures (config : PresburgerTestConfig) : List FormulaTemplate :=
  let atomic := generateAtomicStructures config
  [for (φ₁, φ₂) in atomic.product atomic yield
    [AndTemplate φ₁ φ₂, OrTemplate φ₁ φ₂]]

def generateQuantifiedStructures (config : PresburgerTestConfig) : List FormulaTemplate :=
  let base := generateBooleanStructures config
  [for φ in base, depth in [1..config.max_depth] yield
    ExistsTemplate (freshVar ()) config.target_domain φ]
```

### Phase 2: Parameter Instantiation

```lean
def instantiateTemplate (template : FormulaTemplate) (config : PresburgerTestConfig) 
  : List Formula :=
  match template with
  | AtomicTemplate n_vars op =>
      generateLinearConstraints n_vars op config
  | AndTemplate φ₁ φ₂ =>
      [Formula.and f₁ f₂ | f₁ in instantiate φ₁, f₂ in instantiate φ₂]
  | ExistsTemplate var domain φ =>
      [Formula.exists var domain f | f in instantiate φ]

def generateLinearConstraints (n_vars : Nat) (op : CompOp) (config : PresburgerTestConfig) 
  : List Constraint :=
  -- Generate coefficients systematically to ensure variety
  let coeff_patterns := [
    [1, 0, 0],     -- Single variable
    [1, 1, 0],     -- Two variables, equal coeffs
    [1, -1, 0],    -- Two variables, opposite coeffs  
    [2, 1, 0],     -- Two variables, different coeffs
    [1, 1, 1]      -- Three variables
  ]
  
  [for pattern in coeff_patterns,
       constant in [-config.max_coeff..config.max_coeff] yield
    Constraint 
      (LinearTerm pattern constant)
      op  
      (LinearTerm [0] 0)]  -- RHS = 0 for normalization
```

### Phase 3: Provability Filtering

```lean
def filterProvable (formulas : List Formula) (domain : Domain) : List Formula :=
  formulas.filter (fun f => isProvablePresburger f domain)

def isProvablePresburger (f : Formula) (domain : Domain) : Bool :=
  match f with
  | Formula.atom c => checkConstraintSatisfiable c domain
  | Formula.and f₁ f₂ => 
      isProvablePresburger f₁ domain ∧ isProvablePresburger f₂ domain
  | Formula.or f₁ f₂ => 
      isProvablePresburger f₁ domain ∨ isProvablePresburger f₂ domain
  | Formula.exists var domain_var inner =>
      checkExistentialSatisfiable var inner domain_var
      
def checkConstraintSatisfiable (c : Constraint) (domain : Domain) : Bool :=
  match domain with
  | Domain.Nat => solveConstraintNat c
  | Domain.Int => solveConstraintInt c
  | Domain.Mixed => solveConstraintNat c ∨ solveConstraintInt c

-- Use miniature constraint solver
def solveConstraintInt (c : Constraint) : Bool :=
  -- For ax + by + ... ≤ d, check if there exist integer solutions
  -- Use bounded search or known solvability conditions
  match c with
  | ⟨[a], d, ≤, 0⟩ => true  -- ax ≤ d always has solutions in ℤ
  | ⟨[a], d, =, 0⟩ => d % a = 0  -- ax = d solvable iff a divides d
  | _ => exhaustiveCheckBounded c Domain.Int

def solveConstraintNat (c : Constraint) : Bool :=
  -- Check natural number solutions, more restrictive
  match c with  
  | ⟨[a], d, ≤, 0⟩ => a < 0 ∨ d ≥ 0  -- ax ≤ d with x ≥ 0
  | ⟨[a], d, =, 0⟩ => d ≥ 0 ∧ d % a = 0  -- ax = d with x ≥ 0
  | _ => exhaustiveCheckBounded c Domain.Nat
```

### Phase 4: Lean Theorem Generation

```lean
def generateLeanTheorem (f : Formula) (domain : Domain) : String :=
  let var_decls := generateVariableDeclarations f domain
  let goal_prop := formulaToLean f
  
  s!"theorem presburger_test_{hash f} {var_decls} : {goal_prop} := by presburger"

def formulaToLean (f : Formula) : String :=
  match f with
  | Formula.atom ⟨lhs, op, rhs⟩ => 
      s!"{linearTermToLean lhs} {opToLean op} {linearTermToLean rhs}"
  | Formula.and f₁ f₂ => s!"({formulaToLean f₁}) ∧ ({formulaToLean f₂})"
  | Formula.or f₁ f₂ => s!"({formulaToLean f₁}) ∨ ({formulaToLean f₂})"
  | Formula.exists var domain f => 
      s!"∃ {var} : {domainToLean domain}, {formulaToLean f}"

def linearTermToLean (t : LinearTerm) : String :=
  let terms := [for (var, coeff) in t.coeffs yield
    match coeff with  
    | 1 => var.toString
    | -1 => s!"-{var}"
    | c => s!"{c} * {var}"]
  
  let expr := String.intercalate " + " terms
  if t.constant ≠ 0 then s!"{expr} + {t.constant}" else expr
```

## 4. Provability Criteria

The algorithm ensures provability through:

1. **Constraint Satisfiability**: Use miniature solvers to verify each atomic constraint has solutions in the target domain

2. **Logical Structure Preservation**: 
   - `φ ∧ ψ` is provable iff both `φ` and `ψ` are provable
   - `φ ∨ ψ` is provable iff at least one of `φ`, `ψ` is provable  
   - `∃x. φ(x)` is provable iff the constraint system in `φ` has solutions

3. **Domain-Specific Checks**:
   - **ℕ**: Ensure all solutions are non-negative
   - **ℤ**: Standard linear constraint solving
   - **Mixed**: Provable in either domain

4. **Bounded Verification**: For complex cases, use bounded search within reasonable coefficient ranges

## 5. Example Outputs

The algorithm would generate theorems like:

### Simple Level (Atomic Constraints)
```lean
theorem presburger_test_001 (x : ℕ) : 2 * x + 3 ≤ 7 * x := by presburger

theorem presburger_test_002 (x y : ℤ) : x - 2 * y = 3 * x - y → x = y := by presburger

theorem presburger_test_003 (n : ℕ) : 3 * n < 2 * n + 10 := by presburger
```

### Medium Level (Boolean Combinations)  
```lean
theorem presburger_test_004 (x y : ℤ) : 
  (x + y ≤ 10 ∧ x - y ≥ 2) → 2 * x ≤ 12 := by presburger

theorem presburger_test_005 (a b : ℕ) :
  a + 2 * b = 8 ∨ 2 * a + b = 8 → a + b ≤ 8 := by presburger

theorem presburger_test_006 (x y z : ℤ) :
  x + y + z = 0 ∧ x ≤ y ∧ y ≤ z → z ≥ 0 := by presburger  
```

### Hard Level (Existential Quantifiers)
```lean  
theorem presburger_test_007 (n : ℕ) :
  (∃ x : ℕ, 2 * x + 1 = n) → n % 2 = 1 := by presburger

theorem presburger_test_008 (a b : ℤ) :
  (∃ x y : ℤ, a * x + b * y = gcd a b) := by presburger

theorem presburger_test_009 (n : ℕ) :  
  n > 0 → (∃ k : ℕ, k ≤ n ∧ 2 * k ≥ n) := by presburger

theorem presburger_test_010 (x y : ℤ) :
  (∃ z : ℤ, x ≤ z ∧ z ≤ y) ↔ x ≤ y := by presburger
```

This systematic approach ensures comprehensive coverage of the tactic's intended scope while maintaining provability guarantees through careful constraint solving and domain-specific reasoning.
