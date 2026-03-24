# Tactic Specification: identity_intro

## Original Request

Create a tactic that proves goals of the form A → A (identity implication) by introducing the hypothesis and using assumption

## Analysis

## Tactic Analysis

### 1. Tactic Name
`identity_intro`

### 2. Scope Analysis

**Most general interpretation**: The broadest interpretation would handle any formula that is provable by introducing hypotheses and finding an assumption that matches the conclusion. This could include:
- Simple identity implications: `A → A`
- Nested implications where the conclusion appears among the premises: `A → B → C → A`
- Complex propositions with universal quantifiers: `∀ x, P x → P x`
- Implications involving definitionally equal types

**Lean constraints**: 
- Expression matching in Lean 4 works well for syntactic equality and definitional equality
- The `intro` and `assumption` tactics are well-established and reliable
- Metaprogramming APIs provide good access to goal structure and hypothesis management
- Definitional equality checking is decidable and efficient

**Implementation complexity**: 
- Simple syntactic matching is straightforward
- Handling definitional equality requires careful use of `isDefEq`
- Managing multiple introductions requires iteration but is manageable
- Error handling and reporting can be implemented cleanly

**Chosen scope**: I will target implications of the form `P₁ → P₂ → ... → Pₙ → Q` where `Q` is definitionally equal to one of the `Pᵢ`. This balances generality (handles nested implications and definitional equality) with feasibility (avoids complex unification or proof search).

### 3. Mathematical Specification

**Class of formulas**: `{φ | φ = P₁ → P₂ → ... → Pₙ → Q, n ≥ 1, ∃i ∈ {1,...,n}. Q ≡ Pᵢ}`

where `≡` denotes definitional equality in Lean's type theory.

**Logical fragment**: Propositional logic with implication (extended to dependent types in Lean's type theory)

**Provability conditions**: A formula `P₁ → P₂ → ... → Pₙ → Q` in this class has a proof if and only if there exists some `i ∈ {1,...,n}` such that `Q` is definitionally equal to `Pᵢ`.

**Example formulas**:
- `A → A` (basic identity)
- `A → B → A` (first projection)
- `A → B → C → B` (second of three)
- `Nat → List Nat → Nat` (with definitional equality)

### 4. Purpose
Proves implications where the conclusion is definitionally equal to one of the premises by systematically introducing hypotheses and applying assumption.

### 5. Input Types
- **Goal type**: Any expression of the form `Expr.forallE` (implications/dependent functions)
- **Expected structure**: Nested implications ending in a conclusion that matches one of the introduced premises

### 6. Algorithm

1. **Goal Analysis**: Check if the current goal is an implication (`Expr.forallE`)
2. **Iterative Introduction**: 
   - While the goal is an implication:
     - Apply `intro` tactic to introduce the hypothesis
     - Store the introduced hypothesis
     - Move to the new goal
3. **Assumption Search**: Once no more implications remain:
   - Apply the `assumption` tactic to find a matching hypothesis
   - If `assumption` succeeds, the proof is complete
4. **Verification**: Confirm that the proof term type-checks and solves the original goal

### 7. Success Criteria

**Success**: 
- Goal has the form `P₁ → P₂ → ... → Pₙ → Q`
- After introducing all hypotheses `P₁, P₂, ..., Pₙ`, the `assumption` tactic successfully finds a hypothesis definitionally equal to `Q`
- The resulting proof term type-checks

**Failure**:
- Goal is not an implication
- After introducing all possible hypotheses, no hypothesis matches the conclusion
- Type-checking fails (should not happen with correct implementation)

### 8. Edge Cases

1. **Non-implication goals**: Return informative error message
2. **Zero premises**: Goal is not an implication, should fail gracefully
3. **Multiple matching hypotheses**: `assumption` tactic will pick the first suitable one
4. **Definitional equality**: Handle cases where conclusion is definitionally but not syntactically equal to a premise
5. **Dependent types**: Ensure proper handling of dependent function types where later types may depend on earlier arguments
6. **Universe levels**: Should work automatically through Lean's type system

### 9. Dependencies

```lean
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Intro
import Lean.Elab.Tactic.Assumption
import Lean.Meta.Basic
import Lean.Meta.Tactic.Util.Core
```

**Key APIs needed**:
- `Lean.Elab.Tactic.*` for tactic infrastructure
- `Lean.Meta.intro` for introducing hypotheses
- `Lean.Elab.Tactic.assumption` for finding matching assumptions
- `Lean.Meta.isDefEq` if custom definitional equality checking is needed
- `Lean.Expr.isForall` for checking implication structure

## Test Generation Algorithm

# Test Case Generation Algorithm for `identity_intro` Tactic

## Algorithm Overview

This algorithm generates theorem statements of the form `P₁ → P₂ → ... → Pₙ → Q` where `Q` is definitionally equal to one of the `Pᵢ`, ensuring they are provable by the `identity_intro` tactic.

## 1. Input Parameters

```lean
structure TestGenParams where
  max_depth : Nat := 5          -- Maximum number of premises (1 ≤ n ≤ max_depth)
  num_base_props : Nat := 4      -- Number of distinct base propositions
  include_complex : Bool := true -- Include complex propositions (functions, types)
  include_dependent : Bool := true -- Include dependent types
  num_tests_per_structure : Nat := 10 -- Tests per implication structure
```

## 2. Core Algorithm

### Phase 1: Structure Generation
Generate all possible implication chain lengths and conclusion positions.

```
For depth d from 1 to max_depth:
  For conclusion_position p from 1 to d:
    yield structure (depth=d, target_premise=p)
```

### Phase 2: Proposition Assignment
For each structure, generate valid proposition assignments.

```
function generatePropositionAssignments(structure, params):
  assignments = []
  
  // Simple propositional variables
  for each way to assign variables from {A, B, C, D, ...}:
    assignment = createAssignment(structure, variables)
    if isProvable(assignment, structure):
      assignments.add(assignment)
  
  // Complex types (if enabled)
  if params.include_complex:
    for each complex_type in {Nat, String, List Nat, Nat → Nat, ...}:
      assignment = createMixedAssignment(structure, complex_type)
      if isProvable(assignment, structure):
        assignments.add(assignment)
        
  // Dependent types (if enabled)  
  if params.include_dependent:
    assignment = createDependentAssignment(structure)
    if isProvable(assignment, structure):
      assignments.add(assignment)
      
  return assignments
```

### Phase 3: Provability Verification

```
function isProvable(assignment, structure):
  premises = assignment.premises
  conclusion = assignment.conclusion
  target_premise = premises[structure.target_premise - 1]
  
  // Check if conclusion matches target premise
  return conclusion.isDefEq(target_premise)
```

### Phase 4: Test Case Construction

```
function constructTestCase(assignment, structure):
  premises = assignment.premises
  conclusion = assignment.conclusion
  
  // Build implication chain: P₁ → P₂ → ... → Pₙ → Q
  result = conclusion
  for i from premises.length down to 1:
    result = premises[i-1] → result
    
  return result
```

## 3. Detailed Implementation

### 3.1 Base Proposition Generator
```
function generateBasePropositions(num_props):
  simple = [Prop variables A, B, C, D, ...]  // Take first num_props
  
  complex = [
    Nat, String, Bool, 
    List Nat, Array String,
    Nat → Nat, String → Bool,
    Nat × String, Bool × Nat × String
  ]
  
  dependent = [
    ∀ (n : Nat), Vector Nat n,
    ∀ (α : Type), List α,
    ∀ (p : Nat → Prop), Decidable (p n)
  ]
  
  return simple ∪ complex ∪ dependent
```

### 3.2 Structure Enumeration
```
function enumerateStructures(max_depth):
  structures = []
  
  for depth in 1..max_depth:
    for target_pos in 1..depth:
      structures.add(Structure{
        premise_count: depth,
        target_premise: target_pos,
        description: f"{depth} premises, return premise {target_pos}"
      })
      
  return structures
```

### 3.3 Assignment Generation Strategy
```
function generateAssignments(structure, base_props):
  assignments = []
  n = structure.premise_count
  target = structure.target_premise
  
  // Strategy 1: All same proposition
  for prop in base_props:
    premises = [prop] * n
    conclusion = prop
    assignments.add((premises, conclusion))
    
  // Strategy 2: Target premise different, others same
  for target_prop in base_props:
    for other_prop in base_props:
      if target_prop != other_prop:
        premises = [other_prop] * n
        premises[target-1] = target_prop
        conclusion = target_prop
        assignments.add((premises, conclusion))
        
  // Strategy 3: All different, conclusion matches target
  if n <= len(base_props):
    for permutation in permutations(base_props, n):
      premises = list(permutation)
      conclusion = premises[target-1]
      assignments.add((premises, conclusion))
      
  // Strategy 4: Mixed complexity levels
  for simple_prop in simple_base_props:
    for complex_prop in complex_base_props:
      premises = mix_properties(simple_prop, complex_prop, n)
      conclusion = premises[target-1]
      assignments.add((premises, conclusion))
      
  return assignments
```

## 4. Provability Criteria

A generated theorem `P₁ → P₂ → ... → Pₙ → Q` is provable by `identity_intro` if and only if:

1. **Structural condition**: The formula is a chain of implications ending in a conclusion
2. **Matching condition**: `Q` is definitionally equal to `Pᵢ` for some `i ∈ {1, ..., n}`
3. **Type correctness**: All propositions are well-typed in the current context

```
function verifyProvability(theorem):
  structure = parseImplicationStructure(theorem)
  if structure.isEmpty():
    return false
    
  premises = structure.premises
  conclusion = structure.conclusion
  
  // Check if conclusion matches any premise
  for premise in premises:
    if isDefEq(conclusion, premise):
      return true
      
  return false
```

## 5. Example Outputs

The algorithm would generate theorems like these:

### Basic Cases
1. `A → A` (depth=1, target=1)
2. `A → B → A` (depth=2, target=1) 
3. `A → B → B` (depth=2, target=2)
4. `A → B → C → A` (depth=3, target=1)
5. `A → B → C → B` (depth=3, target=2)

### Type-Based Cases  
6. `Nat → String → Nat` (mixed types, target=1)
7. `(Nat → Nat) → Bool → (Nat → Nat)` (function types, target=1)
8. `List String → Nat × Bool → List String` (complex types, target=1)

### Dependent Type Cases
9. `∀ (α : Type), α → List α → α` (polymorphic, target=1)
10. `∀ (n : Nat), Vector Nat n → Bool → Vector Nat n` (dependent, target=1)

### Complex Nesting
11. `A → B → C → D → E → C` (depth=5, target=3)
12. `(A → B) → C → (A → B)` (nested implications, target=1)

## 6. Implementation Notes

### Edge Case Handling
- **Definitional equality**: Include cases where conclusion and premise are definitionally but not syntactically equal
- **Universe levels**: Generate theorems at different universe levels (Type, Type 1, etc.)
- **Empty context**: Ensure all generated propositions are valid in empty context

### Optimization Strategies
- **Memoization**: Cache provability checks for repeated subformulas
- **Early termination**: Skip obviously unprovable assignments
- **Balanced generation**: Ensure good coverage across all structure types

### Quality Assurance
- **Diversity metrics**: Measure structural and propositional diversity
- **Completeness**: Ensure all valid structures up to max_depth are covered
- **Minimality**: Avoid generating redundant test cases

This algorithm systematically generates comprehensive test cases that thoroughly exercise the `identity_intro` tactic across its intended domain while guaranteeing provability.
