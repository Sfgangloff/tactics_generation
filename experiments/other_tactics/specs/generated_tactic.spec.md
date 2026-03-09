> **User Request:** A tactic that rewrites modulo associativity and commutativity. The tactic `ac_rw [lemmas]` works like `rw` but can match terms up to associativity and commutativity of operators.

Implementation strategy:
1. Maintain a database of ac-constants (constants with associativity and commutativity lemmas)
2. For each rewrite lemma, apply it to metavariables until the type is an equality or iff, with T as the lhs/rhs
3. Find subexpressions in the target location with the same head as T, excluding nested occurrences under the same operator
4. For each subexpression e, check ac-unification with T using custom unification:
   - If head H is not ac-constant: replace ac-arguments with metavariables, unify regularly, then recursively ac-unify ac-arguments
   - If head H is ac-constant: replace last 2 arguments with metavariables, unify regularly, collect argument arrays from both sides, find injective mapping between matching arguments
5. If e ac-unifies with T, use ac-lemmas to reshape e to match T's structure (left-associate then use left_comm for permutation), placing unused arguments to the right
6. Perform the rewrite with the reshaped expression

Example usage: `ac_rw [h, zero_add]` where `h : x + y + z = 0` can rewrite `z + (a + x) + y` to `a` by recognizing the ac-equivalent subexpression.

---

# Tactic Specification: generated_tactic

## Analysis

# Tactic Analysis: `ac_rw`

## 1. Tactic Name
`ac_rw`

## 2. Scope Analysis

**Most general interpretation**: The broadest interpretation would be a tactic that can rewrite any expression modulo any algebraic structure's axioms (associativity, commutativity, idempotency, distributivity, etc.) across arbitrary type classes and operations.

**Lean constraints**: 
- Expression matching and unification APIs have limited support for modulo-equivalence matching
- Type class resolution complexity grows exponentially with the number of operations
- Decidability concerns for general AC-unification (which is NP-complete)
- Limited metaprogramming support for custom unification algorithms

**Implementation complexity**: A fully general AC-rewriting system would require:
- Custom unification algorithms for AC theories
- Efficient canonicalization procedures
- Complex backtracking for multiple possible matches
- Integration with Lean's type class system

**Chosen scope**: Target binary operations with explicit associativity and commutativity instances, focusing on:
- Operations in algebraic structures (Add, Mul, etc.) with `IsAssociative` and `IsCommutative` instances
- Single-step rewrites (no chaining of AC-equivalences)
- Goals that are equalities or can be converted to equalities
- Subexpression matching within reasonable depth limits

This balances practical utility (covers most mathematical use cases) with implementability (leverages existing Lean infrastructure).

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `G` where:
- `G` contains subexpressions `e` built from AC-operators
- There exists a rewrite lemma `l : ∀ x₁...xₙ, P₁ → ... → Pₘ → (f x₁...xₙ = g x₁...xₙ)`
- Some subexpression `e` in `G` is AC-equivalent to `f x₁...xₙ` for some instantiation
- The conditions `P₁...Pₙ` are provable in the current context

**Logical fragment**: First-order logic with equality, restricted to expressions containing binary operators with associativity and commutativity properties.

**Provability conditions**: A goal `G` has a proof via `ac_rw [lemmas]` iff:
1. ∃ lemma `l ∈ lemmas` with conclusion `lhs = rhs`
2. ∃ subexpression `e` in `G` such that `e ≡_AC lhs` (AC-equivalent)
3. All premises of `l` are provable in the current context
4. There exists a sequence of associativity/commutativity rewrites transforming `e` to match `lhs` structurally

## 4. Purpose
Performs rewriting with lemmas while automatically handling associativity and commutativity of operators to match subexpressions that are equivalent modulo AC.

## 5. Input Types
- **Goals**: Any goal containing expressions with AC-operators (typically equality goals)
- **Lemmas**: List of lemmas with equality or iff conclusions
- **AC-operators**: Binary operators with `IsAssociative` and `IsCommutative` instances

## 6. Algorithm

1. **AC-constant detection**: Query type class system for operators with both `IsAssociative` and `IsCommutative` instances

2. **Lemma processing**: For each lemma:
   - Apply to metavariables until conclusion is equality/iff
   - Extract LHS pattern `T`

3. **Subexpression enumeration**: 
   - Traverse goal expression to find all subexpressions with same head as `T`
   - Skip nested occurrences under same AC-operator to avoid redundancy

4. **AC-unification**: For each candidate subexpression `e`:
   - If head is non-AC: standard unification with recursive AC-unification of AC-arguments
   - If head is AC: flatten both `e` and `T` to argument lists, find injective mapping between arguments

5. **Expression reshaping**: If AC-unification succeeds:
   - Left-associate the matched subexpression using associativity lemmas
   - Apply `left_comm` repeatedly to permute arguments to match pattern
   - Place unmatched arguments on the right

6. **Rewrite execution**: Apply the lemma to the reshaped expression

## 7. Success Criteria

**Success**: 
- AC-unification finds a valid mapping between subexpression and lemma pattern
- All lemma premises are provable
- Reshaping produces syntactically matching expressions

**Failure**:
- No AC-equivalent subexpression found
- Lemma premises unprovable  
- AC-unification algorithm fails to find mapping
- Reshaping process fails due to missing AC-lemmas

## 8. Edge Cases

- **Nested AC-operators**: Handle expressions like `(a + b) * (c + d)` correctly
- **Mixed operators**: Operations combining AC and non-AC operators
- **Malformed lemmas**: Lemmas without equality conclusions
- **Infinite loops**: Prevent cyclic rewrites during reshaping
- **Type class failures**: Missing `IsAssociative`/`IsCommutative` instances
- **Performance**: Exponential blowup with deeply nested AC-expressions

## 9. Dependencies

```lean
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic  
import Mathlib.Logic.Basic
import Mathlib.Tactic.Simp.Basic
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Simp.Main
```

Key type classes:
- `IsAssociative`
- `IsCommutative`  
- `Add`, `Mul`, `HAdd`, `HMul`
- Standard algebraic structure classes (`Semigroup`, `CommSemigroup`, etc.)

## Test Generation Algorithm

# Test Case Generation Algorithm for `ac_rw` Tactic

## 1. Input Parameters

```lean
structure ACRwTestConfig where
  max_depth : ℕ := 3                    -- Maximum nesting depth of expressions
  max_terms : ℕ := 5                    -- Maximum terms in AC-flattened expressions
  num_variables : ℕ := 4                -- Number of base variables (a, b, c, d)
  operators : List ACOperator           -- AC operators to test
  lemma_complexity : ℕ := 2             -- Maximum complexity of rewrite lemmas
  goal_types : List GoalType            -- Types of goals to generate

inductive ACOperator
  | add_nat | mul_nat | add_int | mul_int | max_nat | min_nat | union_set | inter_set

inductive GoalType  
  | equality | inequality | membership | structural
```

## 2. Core Algorithm

### Phase 1: AC-Expression Generation

```lean
def generateACExpression (op : ACOperator) (depth : ℕ) (vars : List Variable) : ACExpr :=
  if depth = 0 then
    -- Base case: return variable or constant
    sample vars ∪ {neutral_element op}
  else
    -- Recursive case: build AC-expression
    let num_children := random_range 2 (max_terms + 1)
    let children := (1..num_children).map (λ _ => 
      if random_bool 0.6 then 
        generateACExpression op (depth - 1) vars
      else 
        sample vars)
    ACExpr.op op children

-- Generate all possible AC-equivalent forms
def generateACEquivalents (expr : ACExpr) : List ACExpr :=
  let flattened := flatten expr  -- (a + b) + c ↦ [a, b, c]
  let permutations := all_permutations flattened
  let associations := permutations.bind (λ perm => all_associations perm)
  associations.dedup
```

### Phase 2: Rewrite Lemma Generation

```lean
structure RewriteLemma where
  name : String
  lhs : ACExpr
  rhs : ACExpr  
  premises : List Expr
  operator : ACOperator

def generateRewriteLemmas (op : ACOperator) (complexity : ℕ) : List RewriteLemma :=
  match op with
  | ACOperator.add_nat => [
      ⟨"add_zero", "a + 0", "a", [], op⟩,
      ⟨"zero_add", "0 + a", "a", [], op⟩,
      ⟨"add_comm_specific", "a + b + c", "c + a + b", [], op⟩,
      ⟨"add_assoc_reorder", "(a + b) + (c + d)", "a + (c + (b + d))", [], op⟩,
      ⟨"conditional_simp", "a + b", "b", ["a = 0"], op⟩
    ]
  | ACOperator.mul_nat => [
      ⟨"mul_one", "a * 1", "a", [], op⟩,
      ⟨"one_mul", "1 * a", "a", [], op⟩,  
      ⟨"mul_zero", "a * 0", "0", [], op⟩,
      ⟨"distrib_factor", "a * b + a * c", "a * (b + c)", [], op⟩
    ]
  | _ => generate_generic_lemmas op complexity

def generate_generic_lemmas (op : ACOperator) (complexity : ℕ) : List RewriteLemma :=
  let base_patterns := generate_base_patterns op complexity
  base_patterns.map (λ (lhs, rhs) => 
    ⟨s!"generic_{hash lhs}", lhs, rhs, [], op⟩)
```

### Phase 3: Goal Construction

```lean
def constructGoal (goal_type : GoalType) (lemma : RewriteLemma) (context : ACExpr) : Goal :=
  match goal_type with
  | GoalType.equality =>
      -- Embed LHS in larger expression, goal is to prove equality to RHS version
      let embedded_lhs := embed_subexpression context lemma.lhs
      let embedded_rhs := embed_subexpression context lemma.rhs  
      Goal.eq embedded_lhs embedded_rhs
      
  | GoalType.inequality => 
      -- For ordered structures, create inequality goals
      let embedded := embed_subexpression context lemma.lhs
      Goal.le embedded (simplify embedded lemma.rhs)
      
  | GoalType.structural =>
      -- Goals involving structural properties
      let expr := embed_subexpression context lemma.lhs
      Goal.structural_prop expr (deduce_property lemma.rhs)

def embed_subexpression (context : ACExpr) (target : ACExpr) : ACExpr :=
  -- Randomly choose embedding strategy
  match random_choice ["direct", "left_deep", "right_deep", "mixed"] with
  | "direct" => target
  | "left_deep" => ACExpr.op context.op [target, context]  
  | "right_deep" => ACExpr.op context.op [context, target]
  | "mixed" => 
      let vars := extract_vars context
      let noise := sample vars 2
      ACExpr.op context.op ([target] ++ noise ++ [context])
```

### Phase 4: AC-Unification Verification

```lean
def verifyACUnifiable (goal_expr : ACExpr) (lemma_lhs : ACExpr) (op : ACOperator) : Bool :=
  let goal_subexprs := extract_subexpressions goal_expr op
  goal_subexprs.any (λ subexpr => ac_unify subexpr lemma_lhs op)

def ac_unify (expr1 expr2 : ACExpr) (op : ACOperator) : Bool :=
  if expr1.head ≠ expr2.head then false
  else if expr1.head = op then
    -- AC-unification: flatten and check multiset equality
    let flat1 := flatten_ac expr1 op
    let flat2 := flatten_ac expr2 op  
    multiset_unifiable flat1 flat2
  else
    -- Non-AC head: structural unification with AC-subterms
    expr1.args.zip expr2.args |>.all (λ (a1, a2) => ac_unify a1 a2 op)
```

### Phase 5: Provability Filtering

```lean
def isProvableByACRw (goal : Goal) (lemma : RewriteLemma) : Bool :=
  -- Check basic structure
  goal.contains_ac_subexpr lemma.operator &&
  -- Verify AC-unification possible  
  verifyACUnifiable goal.lhs lemma.lhs lemma.operator &&
  -- Check premise satisfiability
  lemma.premises.all (λ p => provable_in_context p goal.context) &&
  -- Verify no infinite loops in reshaping
  reshaping_terminates goal.lhs lemma.lhs lemma.operator

def reshaping_terminates (expr pattern : ACExpr) (op : ACOperator) : Bool :=
  -- Ensure reshaping process won't loop infinitely
  let reshaping_steps := compute_reshaping_sequence expr pattern op
  reshaping_steps.length < max_reshaping_steps &&
  reshaping_steps.all (λ step => step.well_founded)
```

## 3. Complete Generation Procedure

```lean
def generateACRwTestCases (config : ACRwTestConfig) : List TestCase :=
  let mut test_cases := []
  
  for op in config.operators do
    let lemmas := generateRewriteLemmas op config.lemma_complexity
    let base_vars := generate_variables config.num_variables
    
    for lemma in lemmas do
      for goal_type in config.goal_types do
        for depth in [1..config.max_depth] do
          -- Generate context expressions
          let contexts := (1..5).map (λ _ => 
            generateACExpression op depth base_vars)
          
          for context in contexts do
            let goal := constructGoal goal_type lemma context
            
            -- Verify provability
            if isProvableByACRw goal lemma then
              let test_case := TestCase.mk goal [lemma] op
              test_cases := test_case :: test_cases
  
  test_cases.dedup_by structural_equiv
```

## 4. Provability Criteria

A generated theorem is provable by `ac_rw` if and only if:

1. **Structural Match**: Goal contains subexpression AC-equivalent to some lemma LHS
2. **AC-Unification Success**: The AC-unification algorithm can find variable assignments  
3. **Premise Satisfaction**: All lemma premises are provable in goal context
4. **Reshaping Feasibility**: Associativity/commutativity lemmas exist for required transformations
5. **Termination**: Reshaping process terminates without cycles

## 5. Example Generated Test Cases

### Basic AC-Rewriting
```lean
-- Test 1: Simple commutativity  
example (a b c : ℕ) : a + b + c = c + a + b := by ac_rw [add_comm]

-- Test 2: Nested associativity
example (a b c d : ℕ) : (a + b) + (c + d) = a + (c + (b + d)) := by ac_rw [add_assoc]

-- Test 3: Zero elimination in complex expression
example (a b c : ℕ) : a + (0 + b) + c = a + b + c := by ac_rw [zero_add]
```

### Advanced AC-Structures
```lean
-- Test 4: Multiple operators
example (a b c d : ℕ) : (a + b) * (c + d) = (c + d) * (b + a) := by ac_rw [mul_comm, add_comm]

-- Test 5: Conditional rewriting  
example (a b c : ℕ) (h : a = 0) : a + b + c = b + c := by ac_rw [add_zero] {simp_config := {contextual := true}}

-- Test 6: Deep embedding
example (a b c d e : ℕ) : a + (b + c + d) + e = a + (d + b + c) + e := by ac_rw [add_comm]
```

### Set Operations
```lean  
-- Test 7: Set union AC-rewriting
example (A B C D : Set α) : A ∪ B ∪ C ∪ D = C ∪ A ∪ D ∪ B := by ac_rw [union_comm]

-- Test 8: Mixed set operations
example (A B C : Set α) : A ∪ (B ∩ A) = A ∪ B ∩ A := by ac_rw [union_distrib]
```

### Failure Cases (for negative testing)
```lean
-- Test 9: Non-AC operator (should fail)
example (a b c : ℕ) : a - b - c = c - a - b := by ac_rw [sub_comm] -- FAIL

-- Test 10: Unprovable premise (should fail)  
example (a b : ℕ) : a + b = b := by ac_rw [add_zero] -- FAIL: premise a = 0 unprovable
```

This algorithm systematically generates test cases that exercise the full capabilities of the `ac_rw` tactic while ensuring all generated theorems are provable by the tactic's intended mechanism.
