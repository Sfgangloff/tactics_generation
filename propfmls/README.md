# Propositional Formula Generator

This directory contains Julia code for **automatically generating provable propositional logic theorems** for use in testing and training automated theorem proving systems in Lean 4.

## Overview

The generator creates implication-based propositional formulas (e.g., `(A → B) → ((B → C) → (A → C))`) that are guaranteed to be provable using natural deduction rules. It uses combinatorial methods to:

1. **Enumerate all possible formula shapes** (via Catalan numbers)
2. **Determine which formulas are provable** (via proof search)
3. **Count equivalent formulas** (via equivalence relations and Bell numbers)
4. **Generate Lean theorem statements** ready for automated proving

This is useful for creating benchmark datasets of theorems with controlled complexity for evaluating tactic generation systems.

## Core Components

### 1. Formula Shape Generation (`fml_shape.jl`)

Defines the syntactic structure of propositional formulas as implication chains.

**Key concepts:**
- `FmlShape`: Represents the shape of a formula as a tree of implications
- `generate_catalan(n)`: Generates all Catalan structures for `n` implications
- `catalan_to_fml_shape(catal)`: Converts Catalan structure to formula shape

**Example shapes for n=2:**
```
((1 -> 2) -> 3)     # corresponds to (A → B) → C
(1 -> (2 -> 3))     # corresponds to A → (B → C)
```

### 2. Equivalence Relations (`equivalences.jl`)

Tracks which atomic propositions can be unified while preserving provability.

**Key data structures:**
- `Equivalence`: Partition of formula variables (e.g., A=B, C distinct)
- `EqAC` (Equivalence Anti-Chain): Collection of equivalence relations with no subset relationships
- `bell(n)`: Computes Bell numbers (counts of set partitions) for formula counting

**Operations:**
- `join(eq1, eq2)`: Merges two equivalence relations
- `count_above(eq)`: Counts formulas compatible with an equivalence
- `collect_above(eq)`: Generates all formulas compatible with an equivalence

**Purpose:** Two formulas with different variable labelings may be logically equivalent (e.g., `A → B` ≡ `C → D`). Equivalence relations help avoid generating duplicate theorems.

### 3. Provability Analysis (`provable_count.jl`)

Determines which formulas are provable via backward proof search.

**Key function:**
- `provable_eqac(shape)`: Returns equivalence anti-chain of all variable assignments that make the formula provable

**Algorithm:**
- Performs backward chaining from goal using assumptions
- Tracks hypothesis availability to avoid infinite loops
- Uses equivalence relations to represent all provable variable assignments compactly

**Example:** For shape `(1 -> 2) -> 1`:
- Provable when `1 ≡ 2` (both unify to same proposition)
- Not provable when `1 ≠ 2` (cannot derive arbitrary `A` from `A → B`)

### 4. Theorem Generation (`provable_generate.jl`)

Main script that generates Lean theorem statements.

**Usage:**
```bash
julia provable_generate.jl <num_implications>
```

**Example output for `n=2`:**
```lean
theorem propfmls_2_1_1 (A : Prop) : (A → A) := by sorry
theorem propfmls_2_1_2 (A B : Prop) : (A → (B → A)) := by sorry
theorem propfmls_2_2_1 (A B : Prop) : ((A → B) → B) := by sorry
...
```

**Output format:**
- Theorem name: `propfmls_{n}_{shape_id}_{equivalence_id}`
- Parameters: Atomic propositions used (A, B, C, ...)
- Statement: Implication formula in Lean syntax
- Proof: Placeholder `by sorry` for automated tactic generation

## Mathematical Background

### Catalan Numbers
The number of formula shapes with `n` implications equals the `n`-th Catalan number:
- C₀ = 1, C₁ = 1, C₂ = 2, C₃ = 5, C₄ = 14, ...
- Represents all ways to parenthesize nested implications

### Bell Numbers
The number of ways to partition `k` atomic propositions into equivalence classes:
- B₀ = 1, B₁ = 1, B₂ = 2, B₃ = 5, B₄ = 15, ...
- Used to count distinct variable assignments

### Complexity Growth
For `n` implications:
- Formula shapes: Cₙ (Catalan)
- Variables per formula: up to n+1
- Potential equivalences per shape: Bₙ₊₁ (Bell)
- **Total formulas generated**: Sum over shapes and provable equivalences

## Test Files

- `equivalences_test.jl`: Tests Bell number computation and equivalence operations
- `fml_shape_test.jl`: Tests Catalan generation and formula shape conversion
- `provable_count_test.jl`, `provable_count_test2.jl`, `provable_count_test3.jl`: Tests provability analysis
- `provable_count_ori.jl`: Original/reference implementation

## Integration with Tactic Generation

Generated theorems serve as training/test data for the automated theorem proving pipeline:

1. **Generate theorems:** `julia provable_generate.jl 3 > propositions_3.lean`
2. **Move to Lean project:** Copy output to `TacticsGeneration/Tactics/`
3. **Run tactic generation:** Apply LLM-based proof search to replace `sorry` with actual tactics
4. **Validate:** Use `scripts/fix_lean.py` to verify proofs compile

The theorems are guaranteed to be provable, allowing evaluation of tactic generation success rate and proof complexity.

## Dependencies

**Julia packages:**
- Base Julia only (no external dependencies)

**Julia version:**
- Tested with Julia 1.x

## Running the Generator

```bash
# Generate theorems with 3 implications
julia propfmls/provable_generate.jl 3

# Generate and save to file
julia propfmls/provable_generate.jl 4 > TacticsGeneration/Tactics/propositions_4.lean

# Run tests
julia propfmls/equivalences_test.jl
julia propfmls/fml_shape_test.jl
julia propfmls/provable_count_test.jl
```

## Limitations and Future Work

**Current limitations:**
- Only handles implication formulas (→)
- No conjunction (∧), disjunction (∨), or negation (¬)
- Generates theorems without proofs (requires separate tactic generation)

**Potential extensions:**
- Add support for full propositional logic connectives
- Generate proof hints alongside theorems
- Optimize for larger formula sizes (currently practical up to ~n=5)
- Add difficulty metrics (proof depth, branching factor)
- Generate minimal axiom sets for proving each theorem

## References

- **Catalan numbers:** [OEIS A000108](https://oeis.org/A000108)
- **Bell numbers:** [OEIS A000110](https://oeis.org/A000110)
- **Natural deduction:** Gentzen-style proof systems for intuitionistic logic

---

**Related files in project:**
- `TacticsGeneration/Tactics/propositions_*.lean`: Generated theorem files
- `CLAUDE.md`: Overall project documentation
