# Intuitionistic Logic Pilot

This directory contains the pilot experiment that motivated the spec-first pipeline.

The goal was to generate a Lean 4 tactic that uniformly proves a class of
propositional logic theorems involving only implication (→), using metaprogramming
(`run_tac`). The experiment explored three successive approaches to tactic generation.

---

## Three Approaches

### Approach 1 — Example-driven iteration (`gpt5_iterations/PropositionalLogic1/`)

**Workflow**: Use the Julia code (`formula_enumeration/`) to generate provable
propositions with 2 implications. Ask ChatGPT to write a tactic (using `run_tac`,
with an explicit required format) that proves them uniformly. Then provide examples
with 3 implications, 4, etc., and ask the model to update the tactic to handle the
growing class — observing how it evolves.

**Outcome**: The tactic consistently matched the specific examples it was given but
did not generalize. Each new batch of examples revealed edge cases the model had not
accounted for. The repair loop fixed local errors but introduced new ones; 8 files
document the non-convergence. A key failure: the model explained that
`((P → C) → C) ⇒ C` is not intuitionistically valid in general (true) but failed
to check whether provability held for the *specific* substitution in the test cases.

### Approach 2 — LLM-generated characterization (`gpt5_iterations/PropositionalLogic2/`, `PropositionalLogic3/`)

**Workflow**: Instead of feeding examples directly and asking for a tactic, first ask
the model to *explain* the examples: what mathematical property do all the Julia-generated
propositions share? Then ask it to write the tactic guided by that characterization.

**Outcome**: The model inferred a restricted characterization and produced a cleaner
tactic (one using `whnf + forallE` peeling in PropositionalLogic2, and a recursive
proof-search approach in PropositionalLogic3). PropositionalLogic2 converges in 3 files;
PropositionalLogic3 converges in 2. However the inferred characterization was narrower
than the true class — the model characterized only the cases it had seen.

### Approach 3 — Human-written specification (`prove_impl_tautology.lean`, `prove_paren_impl_taut.lean`, `identity_intro.lean`)

**Workflow**: The researchers write the mathematical specification themselves — precisely
characterizing the class of formulas and the algorithm — then ask the model to implement
the tactic from that spec. The spec is embedded as a `/-! ... -/` doc-comment in the file.

**Outcome**: The most reliable approach. Each file has a clear `## Mathematical Specification`
section defining the formula class and algorithm before any code. The resulting tactic
(`identity_intro`: intros all, then assumption) is correct, concise, and mathematically
well-founded. This approach became the basis for the full spec-first pipeline used
in the `limit_auto` study.

---

## File Map

| File | Approach | Description |
|------|----------|-------------|
| `gpt5_iterations/PropositionalLogic1/` | 1 | 8 files: example-driven, non-converging |
| `gpt5_iterations/PropositionalLogic2/` | 2 | 3 files: LLM characterizes from examples, converges |
| `gpt5_iterations/PropositionalLogic3/` | 2→3 | 2 files: explicit prompt for parenthesized class; converges |
| `prove_impl_tautology.lean` / `.spec.md` | 3 | Human spec: full implication fragment with forward chaining |
| `prove_paren_impl_taut.lean` / `.spec.md` | 3 | Human spec: parenthesized implication tautologies |
| `identity_intro.lean` / `.spec.md` | 3 | Human spec: conclusions equal to one hypothesis; simplest correct tactic |
| `formula_enumeration/` | background | Julia code that generated the test propositions (Catalan × Bell) |

---

## Key Findings

- **Approach 1** shows the failure mode of example-driven iteration: without a semantic
  anchor, the model optimizes for the examples rather than the underlying class.
- **Approach 2** is an improvement — asking for a characterization before the code
  helps — but the model-inferred characterization is still incomplete.
- **Approach 3** (researcher writes the spec) is the most reliable. The model is a good
  code generator when given a precise mathematical description; it is a poor
  mathematician when asked to infer the class from examples alone.

This motivated the spec-first pipeline: always generate a formal mathematical specification
(via the `analyze_request` prompt stage) before asking the model to write code.
