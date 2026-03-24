> **User Request:** A tactic for deciding statements in the first-order theory of lists. This handles goals involving list operations like length, concatenation, membership, and structural properties. It can prove statements about list equality, length relationships, and membership predicates. The tactic may use lookup tables for common list property patterns to improve performance.

---

# Tactic Specification: decide_list_theory

## Analysis

# Tactic Analysis: List Theory Decision Procedure

## 1. Tactic Name
`decide_list_theory`

## 2. Scope Analysis

**Most general interpretation**: A complete decision procedure for the first-order theory of lists with all standard operations (length, concatenation, membership, head, tail, etc.), quantifiers over both elements and lists, and arbitrary nesting of operations.

**Lean constraints**: 
- Lean's metaprogramming requires constructive proofs, not just decidability certificates
- Expression matching and unification are limited to syntactic patterns
- No built-in SMT solver integration
- Must work with Lean's type system and definitional equality
- Limited reflection capabilities for arbitrary formulas

**Implementation complexity**:
- Full first-order theory with quantifiers would require sophisticated proof search
- Arbitrary nesting of operations creates exponential complexity
- Maintaining lookup tables for all patterns is impractical
- Need to interface with existing Mathlib automation

**Chosen scope**: Target quantifier-free formulas over concrete list operations with bounded nesting depth. Focus on goals that can be reduced to combinations of:
- List equality via structural decomposition
- Length arithmetic (delegated to `omega`)  
- Membership proofs via case analysis
- Simple concatenation properties

This balances practical utility with implementation feasibility while leveraging Lean's existing decision procedures.

## 3. Mathematical Specification

**Logical fragment**: Quantifier-free first-order logic over the signature `{[], (::), length, (++), (∈), (=)}`

**Formula class**: Let `T` be the set of terms built from:
- List constructors: `[]`, `a :: l`
- Operations: `length(l)`, `l₁ ++ l₂`  
- Variables: list variables and element variables

The tactic handles formulas `φ` where:
```
φ ∈ {t₁ = t₂, t₁ ≠ t₂, a ∈ l, a ∉ l, n₁ ≤ n₂, n₁ < n₂ | t₁,t₂ ∈ T_list, a ∈ T_elem, l ∈ T_list, n₁,n₂ ∈ T_nat}
     ∪ {φ₁ ∧ φ₂, φ₁ ∨ φ₂, ¬φ₁ | φ₁,φ₂ recursively in this set}
```

**Provability conditions**: A formula `φ` is provable iff:
1. List equalities can be established by structural induction and definitional unfolding
2. Length relationships reduce to arithmetic facts provable by `omega`
3. Membership claims can be resolved by finite case analysis on list structure
4. All subformulas are in the supported fragment

## 4. Purpose
Automatically proves or disproves quantifier-free statements about list equality, length relationships, and membership using structural decomposition and arithmetic reasoning.

## 5. Input Types
- **Goals**: `Prop` expressions containing list operations over types `List α` where `α` has decidable equality
- **Context**: May use hypotheses of the same form as additional facts

## 6. Algorithm

1. **Goal Analysis**: Parse the goal to identify list operations and logical structure
2. **Normalization**: Simplify expressions using definitional equalities:
   - `length [] = 0`
   - `length (a :: l) = 1 + length l`  
   - `[] ++ l = l`, `(a :: l₁) ++ l₂ = a :: (l₁ ++ l₂)`
3. **Case Splitting**: For membership goals `a ∈ l`, perform structural induction on `l`
4. **Arithmetic Delegation**: Extract length constraints and pass to `omega` tactic
5. **Structural Comparison**: For list equality `l₁ = l₂`, compare constructors and recurse
6. **Proof Construction**: Build proof terms using appropriate lemmas from `List` namespace
7. **Lookup Optimization**: Cache common patterns like `length (l₁ ++ l₂) = length l₁ + length l₂`

## 7. Success Criteria

**Success**: Goal is closed when all subgoals reduce to:
- Trivial equalities (`rfl`)
- Arithmetic facts solvable by `omega`
- Contradictions exposing `False`

**Failure**: Tactic fails with informative error when:
- Quantifiers are present
- Unsupported operations appear (e.g., `List.reverse`, `List.filter`)
- Decidable equality is unavailable for element type
- Goal exceeds complexity bounds (depth > 10, term size > 100)

## 8. Edge Cases

- **Empty lists**: Handle `[] = []` and `a ∉ []` as base cases
- **Variable lists**: Use `cases` tactic for case analysis when structure unknown  
- **Type inference**: Ensure element types are properly inferred in membership goals
- **Definitional equality**: Leverage `simp` for definitional simplifications
- **Cyclic reasoning**: Detect and avoid infinite recursion in structural decomposition

## 9. Dependencies

```lean
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Length  
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Simp
import Lean.Elab.Tactic
import Lean.Meta.Basic
```

**Key lemmas needed**:
- `List.length_cons`, `List.length_append`
- `List.mem_cons_iff`, `List.mem_append`  
- `List.cons_inj`, `List.append_assoc`
- Decidability instances for `List.mem` and `List.eq`

## Test Generation Algorithm

# Test Case Generation Algorithm for `decide_list_theory`

## 1. Input Parameters

```lean
structure TestGenConfig where
  max_list_depth : Nat := 4        -- Maximum nesting level for list constructors
  max_term_size : Nat := 15         -- Maximum total term size
  num_list_vars : Nat := 3          -- Number of list variables (l₁, l₂, l₃)
  num_elem_vars : Nat := 3          -- Number of element variables (a, b, c)
  max_formula_depth : Nat := 3      -- Maximum logical connective nesting
  include_negations : Bool := true   -- Whether to include negated subformulas
  concrete_list_prob : Float := 0.4 -- Probability of using concrete lists vs variables
```

## 2. Core Algorithm

### Phase 1: Term Generation

**List Term Grammar:**
```
ListTerm := Var(name) 
         | Nil 
         | Cons(ElemTerm, ListTerm)
         | Append(ListTerm, ListTerm)

ElemTerm := Var(name) | Concrete(value)

ArithTerm := Length(ListTerm) | Nat(value) | Add(ArithTerm, ArithTerm)
```

**Term Generation Procedure:**
```lean
def generateListTerm (depth : Nat) (config : TestGenConfig) : ListTerm :=
  if depth = 0 then
    -- Base case: variable or empty list
    if Random.float() < 0.3 then Nil 
    else Var(Random.choice ["l₁", "l₂", "l₃"])
  else
    match Random.weighted_choice with
    | 0.2 => Nil
    | 0.3 => Var(Random.choice list_vars)
    | 0.25 => Cons(generateElemTerm(), generateListTerm(depth-1))
    | 0.25 => Append(generateListTerm(depth-1), generateListTerm(depth-1))
```

### Phase 2: Atomic Formula Generation

**Atomic Formula Types:**
1. **List Equality**: `t₁ = t₂` where both are list terms
2. **List Inequality**: `t₁ ≠ t₂`  
3. **Membership**: `a ∈ l` where `a` is element term, `l` is list term
4. **Non-membership**: `a ∉ l`
5. **Length Relations**: `length(l₁) = length(l₂)`, `length(l) = n`, `length(l₁) ≤ length(l₂)`

```lean
def generateAtomicFormula (config : TestGenConfig) : Formula :=
  match Random.weighted_choice with
  | 0.25 => ListEq(generateListTerm(config.max_list_depth), generateListTerm(config.max_list_depth))
  | 0.15 => ListNeq(generateListTerm(config.max_list_depth), generateListTerm(config.max_list_depth))
  | 0.2 => Membership(generateElemTerm(), generateListTerm(config.max_list_depth))
  | 0.15 => NonMembership(generateElemTerm(), generateListTerm(config.max_list_depth))
  | 0.25 => LengthRel(generateArithTerm(), generateArithTerm())
```

### Phase 3: Formula Structure Generation

**Logical Structure Templates:**
1. **Simple**: Single atomic formula
2. **Conjunction**: `φ₁ ∧ φ₂ ∧ ... ∧ φₙ`
3. **Disjunction**: `φ₁ ∨ φ₂ ∨ ... ∨ φₙ`
4. **Implication Chain**: `φ₁ → φ₂ → ... → φₙ`
5. **Mixed**: `(φ₁ ∧ φ₂) → (φ₃ ∨ φ₄)`

```lean
def generateFormulaStructure (depth : Nat) : Formula :=
  if depth = 0 then generateAtomicFormula()
  else
    match Random.weighted_choice with
    | 0.4 => generateAtomicFormula()
    | 0.2 => And(generateFormulaStructure(depth-1), generateFormulaStructure(depth-1))
    | 0.2 => Or(generateFormulaStructure(depth-1), generateFormulaStructure(depth-1))
    | 0.15 => Implies(generateFormulaStructure(depth-1), generateFormulaStructure(depth-1))
    | 0.05 => Not(generateFormulaStructure(depth-1))
```

### Phase 4: Provability Filtering

**Provability Patterns** (ensure generated theorems are provable):

1. **Tautology Patterns**:
   - `l = l` (reflexivity)
   - `length(l₁ ++ l₂) = length(l₁) + length(l₂)`
   - `a ∈ (a :: l)`
   - `¬(a ∈ [])`

2. **Contradiction Elimination**:
   - Avoid `[] = [a]` 
   - Avoid `length([]) > 0`
   - Check membership consistency

3. **Constructive Validity Check**:
```lean
def isProvable (formula : Formula) : Bool :=
  match formula with
  | ListEq(t₁, t₂) => structurallyEqual(t₁, t₂) ∨ definitionallyEqual(t₁, t₂)
  | Membership(a, Cons(b, l)) => (a = b) ∨ provableMember(a, l)
  | LengthRel(len₁, len₂) => arithmeticallyValid(len₁, len₂)
  | And(φ₁, φ₂) => isProvable(φ₁) ∧ isProvable(φ₂)
  | Implies(φ₁, φ₂) => ¬isProvable(φ₁) ∨ isProvable(φ₂)
  -- etc.
```

### Phase 5: Test Case Assembly

**Final Generation Loop:**
```lean
def generateTestCases (config : TestGenConfig) (count : Nat) : List Formula :=
  let candidates := (1..count*3).map (λ _ => generateFormulaStructure(config.max_formula_depth))
  let provable := candidates.filter isProvable
  let diverse := removeSimilar(provable)  -- Remove structurally similar formulas
  diverse.take(count)
```

## 3. Provability Criteria

### Structural Decidability Rules:

1. **List Equality**: Provable iff terms reduce to same normal form under:
   - `[] ++ l ~> l`
   - `(a::l₁) ++ l₂ ~> a::(l₁ ++ l₂)`
   - Constructor injectivity

2. **Membership**: Provable iff:
   - `a ∈ (a::l)` (immediate)
   - `a ∈ (b::l)` where `a ≠ b` requires `a ∈ l` provable
   - `a ∈ (l₁ ++ l₂)` reduces to `a ∈ l₁ ∨ a ∈ l₂`

3. **Length Relations**: Provable iff arithmetic constraint is valid:
   - Extract length expressions as linear arithmetic
   - Use omega-decidable fragment checker

4. **Logical Structure**: Standard propositional validity with constructive restrictions

## 4. Example Outputs

The algorithm would generate test cases like:

### Basic Structural Properties
```lean
theorem test_1 : ∀ (l : List ℕ), l ++ [] = l := by decide_list_theory

theorem test_2 : ∀ (a : ℕ) (l : List ℕ), length (a :: l) = length l + 1 := by decide_list_theory
```

### Membership Relations  
```lean
theorem test_3 : ∀ (a b : ℕ) (l : List ℕ), a ∈ (b :: l) → a = b ∨ a ∈ l := by decide_list_theory

theorem test_4 : ∀ (a : ℕ), ¬(a ∈ ([] : List ℕ)) := by decide_list_theory
```

### Combined Properties
```lean
theorem test_5 : ∀ (l₁ l₂ : List ℕ), 
  length l₁ = 2 → length l₂ = 3 → length (l₁ ++ l₂) = 5 := by decide_list_theory

theorem test_6 : ∀ (a : ℕ) (l₁ l₂ : List ℕ),
  a ∈ l₁ → a ∈ (l₁ ++ l₂) := by decide_list_theory
```

### Complex Logical Combinations
```lean
theorem test_7 : ∀ (a b : ℕ) (l : List ℕ),
  (a ∈ l ∧ b ∈ l) → (a ∈ (b :: l) ∨ length l > 0) := by decide_list_theory

theorem test_8 : ∀ (l₁ l₂ l₃ : List ℕ),
  l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ := by decide_list_theory
```

### Concrete List Examples
```lean
theorem test_9 : [1, 2] ++ [3] = [1, 2, 3] := by decide_list_theory

theorem test_10 : 2 ∈ [1, 2, 3] ∧ length [1, 2, 3] = 3 := by decide_list_theory
```

This algorithm systematically explores the space of quantifier-free list theory formulas while ensuring all generated test cases are within the tactic's decidable fragment and provable using the specified techniques.
