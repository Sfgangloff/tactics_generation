# Intuitionistic Logic Pilot

This directory contains the pilot experiment that motivated the spec-first approach.

The goal was to generate a Lean 4 tactic that proves the implication fragment of
intuitionistic propositional logic (goals of the form `A → B → ... → C`).

## Files

- `prove_impl_tautology.lean` / `.spec.md` — first iteration
- `prove_paren_impl_taut.lean` / `.spec.md` — refined version
- `identity_intro.lean` / `.spec.md` — identity/intro variant

## Key finding

Two approaches were tried:
1. **Iterative**: generate examples, feed compiler errors back, adapt — slow and fragile.
2. **Spec-first**: ask the LLM to characterize the class in natural language, then generate
   — significantly more efficient.

The gas-bounded search in the final tactic works as a tool but is not mathematically
complete. This motivated the more rigorous spec-first pipeline used for `limit_auto`.

Note: the main development of this pilot is on a separate branch. These files are the
outputs that were committed to this branch.
