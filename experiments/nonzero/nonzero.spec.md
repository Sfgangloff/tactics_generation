> **User Request:** A tactic that proves goals of the form `expr ≠ 0`. The tactic should be at least as powerful as the nonzero-proving component currently used by `field_simp`. It applies various strategies: (1) Uses built-in lemmas for algebraic operations like `a ≠ 0 → -a ≠ 0`, `a ≠ 0 → b ≠ 0 → a * b ≠ 0`, and `a ≠ 0 → a ^ n ≠ 0`; (2) For expressions with head symbols it cannot handle directly (e.g., addition `+`), it falls back to the `positivity` tactic when there is a `PartialOrder` instance available; (3) Combines multiple proof strategies similar to `field_simp`'s current approach for maximum effectiveness.

---

# Tactic Specification: nonzero

## Analysis

# Tactic Analysis: `nonzero`

## 1. Tactic Name
`nonzero`

## 2. Scope Analysis

**Most general interpretation**: A tactic that could prove any goal of the form `expr ≠ 0` for arbitrary expressions in any algebraic structure, using any available algebraic properties, positivity information, and computational methods.

**Lean constraints**: 
- Expression pattern matching is limited to syntactic structure
- Type class resolution must be decidable at tactic time
- Cannot perform arbitrary symbolic computation or equation solving
- Must work with Lean's definitional equality and available simp lemmas
- Positivity tactic integration requires compatible type class instances

**Implementation complexity**:
- Recursive expression decomposition is straightforward
- Integration with existing tactics (`positivity`, `simp`) is well-supported
- Extensibility through lemma databases is standard practice
- Type class instance synthesis adds moderate complexity

**Chosen scope**: Target algebraic expressions in structures with `Zero`, `Neg`, `Mul`, `Pow`, and optionally `PartialOrder` instances. Handle compositions of negation, multiplication, and exponentiation through built-in algebraic lemmas, with fallback to `positivity` for additive expressions and unknown operations when ordering is available. This balances broad applicability with implementation feasibility while matching the user's specific requirements.

## 3. Mathematical Specification

**Class of formulas**: Goals of the form `e ≠ 0` where `e` is an algebraic expression in a type `α` with `Zero α`, and the tactic can construct a proof using:
- Algebraic closure properties: `{e ≠ 0 | ∃ proof via negation, multiplication, or power lemmas}`
- Positivity-based proofs: `{e ≠ 0 | ∃ PartialOrder α ∧ positivity_tactic_succeeds(e > 0)}`

**Logical fragment**: First-order logic with equality and algebraic operations, operating on goals in the decidable fragment of algebraic non-zeroness.

**Provability conditions**: A goal `e ≠ 0` is provable if:
1. `e` syntactically matches `−f` and `f ≠ 0` is provable, OR
2. `e` syntactically matches `f * g` and both `f ≠ 0` and `g ≠ 0` are provable, OR  
3. `e` syntactically matches `f ^ n` where `n > 0` and `f ≠ 0` is provable, OR
4. `e` has `PartialOrder` available and `positivity` can prove `e > 0`, OR
5. `e` simplifies via `simp` to an expression satisfying one of the above conditions

## 4. Purpose
A tactic that proves goals of the form `expr ≠ 0` using algebraic lemmas and positivity reasoning.

## 5. Input Types
- **Goal**: `e ≠ 0` where `e : α` and `[Zero α]`
- **Context**: Local hypotheses of the form `f ≠ 0` for subexpressions `f`

## 6. Algorithm

1. **Goal Structure Check**: Verify goal has form `e ≠ 0`
2. **Expression Analysis**: Pattern match on `e`:
   - If `e = −f`: recursively prove `f ≠ 0`, then apply `neg_ne_zero.mpr`
   - If `e = f * g`: recursively prove `f ≠ 0` and `g ≠ 0`, then apply `mul_ne_zero`
   - If `e = f ^ n` where `n > 0`: recursively prove `f ≠ 0`, then apply `pow_ne_zero`
3. **Base Case Handling**: 
   - Check local context for matching hypothesis
   - Try `simp` to simplify expression
4. **Positivity Fallback**: If above fails and `PartialOrder` instance exists:
   - Call `positivity` tactic on goal `0 < e`
   - If successful, apply `ne_of_gt`
5. **Proof Construction**: Combine subproofs using appropriate lemmas

## 7. Success Criteria
- **Success**: Goal is closed by constructing a proof term of type `e ≠ 0`
- **Failure**: Expression structure not recognized AND positivity fallback fails/unavailable

## 8. Edge Cases
- **Zero expressions**: `0 ≠ 0` should fail gracefully with informative error
- **Complex nested expressions**: May hit recursion limits; bound recursion depth
- **Missing type class instances**: Graceful degradation when `Neg`, `Mul`, `Pow`, or `PartialOrder` unavailable  
- **Non-literal exponents**: `f ^ g` where `g` not provably positive should be handled carefully
- **Definitional equality**: Use `simp` to normalize expressions before pattern matching

## 9. Dependencies
```lean
import Mathlib.Algebra.Order.Positive.Basic  -- for positivity tactic
import Mathlib.Algebra.GroupWithZero.Basic   -- for mul_ne_zero, etc.
import Mathlib.Algebra.Group.Basic           -- for neg_ne_zero
import Mathlib.Algebra.GroupPower.Basic      -- for pow_ne_zero
import Mathlib.Tactic.Positivity             -- for positivity integration
import Mathlib.Tactic.FieldSimp             -- to study existing implementation
```

## Test Generation Algorithm

# Test Case Generation Algorithm for `nonzero` Tactic

## 1. Input Parameters

```lean
structure NonzeroTestConfig where
  max_depth : Nat := 3           -- Maximum nesting depth of expressions
  num_base_vars : Nat := 4       -- Number of distinct base variables (a, b, c, d)
  include_constants : Bool := true -- Include numeric constants (1, 2, -1)
  max_exponent : Nat := 3        -- Maximum literal exponent value
  algebraic_structures : List AlgStruct := [Ring, Field, OrderedRing] 
  hypothesis_prob : Float := 0.7  -- Probability of including helpful hypotheses
```

## 2. Core Algorithm

### Step 1: Expression Structure Generation

**Expression Grammar**:
```
Expr ::= BaseVar | Constant | NegExpr | MulExpr | PowExpr | AddExpr
BaseVar ::= a | b | c | d | ...
Constant ::= 1 | 2 | 3 | -1 | -2 | π | e
NegExpr ::= -Expr
MulExpr ::= Expr * Expr
PowExpr ::= Expr ^ NatLit  
AddExpr ::= Expr + Expr | Expr - Expr
```

**Generation Strategy**:
```python
def generate_expression(depth: int, config: NonzeroTestConfig) -> Expr:
    if depth == 0:
        return random_choice([
            random_base_var(config.num_base_vars),
            random_nonzero_constant() if config.include_constants else None
        ])
    
    expr_type = weighted_choice([
        (NegExpr, 0.15),
        (MulExpr, 0.4),   # Higher weight - main target of tactic
        (PowExpr, 0.25),  # Higher weight - main target of tactic  
        (AddExpr, 0.2)    # Lower weight - handled by positivity fallback
    ])
    
    match expr_type:
        case NegExpr:
            return Neg(generate_expression(depth-1, config))
        case MulExpr:
            return Mul(
                generate_expression(depth-1, config),
                generate_expression(depth-1, config)
            )
        case PowExpr:
            base = generate_expression(depth-1, config)
            exp = random_int(1, config.max_exponent)
            return Pow(base, exp)
        case AddExpr:
            return Add(
                generate_expression(depth-1, config),
                generate_expression(depth-1, config)
            )
```

### Step 2: Provability Analysis

**Provability Tree Construction**:
```python
def is_provable_nonzero(expr: Expr, hypotheses: Set[Expr]) -> bool:
    # Check if expression directly appears in hypotheses
    if f"{expr} ≠ 0" in hypotheses:
        return True
    
    match expr:
        case Neg(f):
            return is_provable_nonzero(f, hypotheses)
        
        case Mul(f, g):
            return (is_provable_nonzero(f, hypotheses) and 
                   is_provable_nonzero(g, hypotheses))
        
        case Pow(f, n) if n > 0:
            return is_provable_nonzero(f, hypotheses)
        
        case Add(f, g):
            # Only provable if positivity can handle it
            return is_provable_positive(expr, hypotheses)
        
        case Constant(c) if c != 0:
            return True
        
        case _:
            return False

def is_provable_positive(expr: Expr, hypotheses: Set[Expr]) -> bool:
    """Simulate what the positivity tactic can prove"""
    match expr:
        case Constant(c) if c > 0:
            return True
        case Mul(f, g):
            return (is_provable_positive(f, hypotheses) and 
                   is_provable_positive(g, hypotheses))
        case Pow(f, n) if n > 0 and n % 2 == 0:
            return is_provable_nonzero(f, hypotheses)
        case Pow(f, n) if n > 0:
            return is_provable_positive(f, hypotheses)
        case Add(f, g):
            return (is_provable_positive(f, hypotheses) and 
                   is_provable_positive(g, hypotheses))
        case BaseVar(v) if f"{v} > 0" in hypotheses:
            return True
        case _:
            return False
```

### Step 3: Hypothesis Generation

**Hypothesis Strategy**:
```python
def generate_hypotheses(target_expr: Expr, config: NonzeroTestConfig) -> Set[str]:
    required_hyps = collect_required_hypotheses(target_expr)
    helpful_hyps = collect_helpful_hypotheses(target_expr)
    
    hypotheses = set(required_hyps)
    
    # Add helpful hypotheses with probability
    for hyp in helpful_hyps:
        if random() < config.hypothesis_prob:
            hypotheses.add(hyp)
    
    return hypotheses

def collect_required_hypotheses(expr: Expr) -> List[str]:
    """Hypotheses needed to make the expression provably nonzero"""
    match expr:
        case BaseVar(v):
            return [f"{v} ≠ 0"]
        case Neg(f):
            return collect_required_hypotheses(f)
        case Mul(f, g):
            return (collect_required_hypotheses(f) + 
                   collect_required_hypotheses(g))
        case Pow(f, n):
            return collect_required_hypotheses(f)
        case Add(f, g):
            # For positivity fallback
            base_vars = collect_base_vars(expr)
            return [f"{v} > 0" for v in base_vars]
        case _:
            return []
```

### Step 4: Test Case Assembly

```python
def generate_test_case(config: NonzeroTestConfig) -> TestCase:
    # Generate target expression
    target = generate_expression(config.max_depth, config)
    
    # Generate hypotheses that make it provable
    hypotheses = generate_hypotheses(target, config)
    
    # Verify provability
    if not is_provable_nonzero(target, hypotheses):
        return None  # Retry
    
    # Choose algebraic structure
    structure = random_choice(config.algebraic_structures)
    
    # Format as theorem
    return TestCase(
        structure=structure,
        hypotheses=list(hypotheses),
        goal=f"{target} ≠ 0"
    )

def generate_test_suite(config: NonzeroTestConfig, num_tests: int) -> List[TestCase]:
    tests = []
    attempts = 0
    max_attempts = num_tests * 10
    
    while len(tests) < num_tests and attempts < max_attempts:
        test = generate_test_case(config)
        if test is not None:
            tests.append(test)
        attempts += 1
    
    return tests
```

## 3. Provability Criteria

A generated theorem `H₁, H₂, ..., Hₙ ⊢ e ≠ 0` is **provable** by the `nonzero` tactic if:

1. **Structural Recursion**: The expression `e` can be decomposed using the tactic's pattern matching rules until reaching base cases
2. **Base Case Coverage**: All base cases are either:
   - Nonzero constants (`1 ≠ 0`, `2 ≠ 0`, etc.)
   - Variables with nonzero hypotheses (`a ≠ 0` in context)
   - Expressions provable by positivity (`a + b > 0` when `a > 0, b > 0`)
3. **Type Class Availability**: Required instances (`Zero`, `Mul`, `Pow`, optionally `PartialOrder`) exist
4. **Termination**: Recursion depth is bounded and decreases at each step

## 4. Example Outputs

Here are 10 example theorem statements the algorithm would generate:

### Basic Algebraic Cases
```lean
-- Test 1: Simple negation
example [Ring α] (a : α) (ha : a ≠ 0) : -a ≠ 0 := by nonzero

-- Test 2: Product of variables  
example [Ring α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by nonzero

-- Test 3: Power with literal exponent
example [Ring α] (a : α) (ha : a ≠ 0) : a ^ 3 ≠ 0 := by nonzero
```

### Nested Expressions
```lean
-- Test 4: Negation of product
example [Ring α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : -(a * b) ≠ 0 := by nonzero

-- Test 5: Product of powers
example [Ring α] (a b : α) (ha : a ≠ 0) (hb : b ≠ 0) : a^2 * b^3 ≠ 0 := by nonzero

-- Test 6: Power of negation
example [Ring α] (a : α) (ha : a ≠ 0) : (-a)^4 ≠ 0 := by nonzero
```

### Positivity Fallback Cases  
```lean
-- Test 7: Sum of positive variables
example [OrderedRing α] (a b : α) (ha : 0 < a) (hb : 0 < b) : a + b ≠ 0 := by nonzero

-- Test 8: Mixed additive/multiplicative
example [OrderedRing α] (a b c : α) (ha : 0 < a) (hb : b ≠ 0) : a + b * c^2 ≠ 0 := by nonzero
```

### Constants and Field Cases
```lean  
-- Test 9: Field with constants
example [Field ℚ] (a : ℚ) (ha : a ≠ 0) : 2 * a + (-1) * a ≠ 0 := by nonzero

-- Test 10: Complex nested structure  
example [OrderedRing ℝ] (x y : ℝ) (hx : x ≠ 0) (hy : 0 < y) : 
  -(x^2) * (y + 1)^3 ≠ 0 := by nonzero
```

## 5. Coverage Analysis

The algorithm ensures comprehensive coverage by:

1. **Syntactic Coverage**: Systematically generates all expression patterns the tactic handles
2. **Depth Stratification**: Tests expressions at different nesting levels  
3. **Hypothesis Variation**: Includes minimal, sufficient, and over-specified hypothesis sets
4. **Structure Diversity**: Tests across different algebraic structures (rings, fields, ordered structures)
5. **Edge Case Inclusion**: Generates cases that test boundary conditions and error paths

This systematic approach ensures the generated test suite thoroughly validates the `nonzero` tactic's correctness and robustness.
