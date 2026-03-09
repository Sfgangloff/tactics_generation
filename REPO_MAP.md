# Repository Map

Annotated guide to the repository for the paper:

> **Generating Lean 4 Tactics from User Specifications: An Empirical Study of
> LLM-Assisted Metaprogramming Strategies** (ITP short paper)

---

## Paper-critical material

```
paper/
  main.tex                        ← paper draft (LaTeX)
  paper_plan.md                   ← section outline and evidence table

experiments/
  intuitionistic_pilot/           ← Section 3: pilot experiment
    README.md
    prove_impl_tautology.lean/spec.md   ← iterative approach output
    prove_paren_impl_taut.lean/spec.md  ← refined iterative version
    identity_intro.lean/spec.md         ← spec-first approach output
    gpt5_iterations/              ← GPT-5 iterative development (13 files)
      README.md                   ← explains PropositionalLogic1/2/3
      PropositionalLogic1/        ← 8 files: non-converging iterative approach
      PropositionalLogic2/        ← 3 files: intermediate
      PropositionalLogic3/        ← 2 files: spec-first, final working version

  limit_auto/                     ← Section 4: main 2×2 study
    spec.md                       ← shared specification (all 4 conditions)
    README.md                     ← study design and results summary
    one_run/
      limit_auto.one_run.lean     ← Condition A: empty (no plan, no LSP)
    plan_without_lsp/             ← Condition B: plan, no LSP
      plan.md
      milestone1.lean … milestone5.lean
    one_shot_with_lsp/            ← Condition C: no plan, with LSP
      output.lean
    plan_with_lsp/                ← Condition D: plan + LSP (best)
      plan.md
      lsp_log.md                  ← complete LSP tool call record
      milestone1.lean … milestone9.lean

  other_tactics/                  ← Section 7 future work
    README.md
    decide_list_theory/           ← second complete tactic (plan + LSP)
    specs/                        ← 12 drafted specs, not yet implemented
```

---

## Pipeline implementation (describes the method, Conditions A and B)

```
pipeline/
  config.py                       ← Config dataclass
  generator.py                    ← 6-stage pipeline orchestrator
  validator.py                    ← Lake compilation wrapper
  models/                         ← LLM providers (Anthropic, OpenAI, OpenRouter)
  prompts/                        ← prompt templates (8 files)
    analyze_request.txt           ← spec extraction
    generate_tactic.txt           ← Lean 4 code generation
    generate_test_algorithm.txt   ← test enumeration strategy
    generate_tests.txt            ← test instantiation
    fix_errors.txt                ← self-correction repair
    split_specifications.txt      ← batch: detect multiple tactics in one spec
    generate_additional_tests.txt ← update mode
    update_tactic.txt             ← update mode

main.py                           ← CLI entry point (single / batch / update)
specifications.json               ← batch mode tactic descriptions
```

---

## Lean project (needed for tactic compilation)

```
Main.lean
lakefile.toml
lean-toolchain
lake-manifest.json
```

---

## Background / historical context

```
propfmls/                         ← Julia code: propositional formula enumeration
                                     used to generate test data for the pilot
                                     (Catalan numbers × provable assignments)

pipeline/legacy/
  README.md
  scripts/
    fix_lean.py                   ← original iterative repair loop (predecessor
    fix_tactic_file.py              to generator.py — relevant for paper §4)
    fix_tactic_focused.py
    README_fix_tactic.md
  prompts/
    metaprogramming_tutorial.txt  ← Lean tactic guide injected into prompts
    fix_tactic_system.txt         ← earlier repair system prompt
  agents_search/                  ← pre-LSP semantic search agent (GPT-4o-mini)
    README.md                       predecessor to lean_leansearch / lean_loogle
    src/                            LSP tools — relevant for paper §5 (discussion)
    data/lean_index.json
    data/enriched_lean_index.json
```

---

## Gitignored (not in repository)

```
output/            ← raw pipeline outputs (local only, subsumed by experiments/)
math_experiments/  ← unrelated experiments
memory/            ← Claude Code session memory
results.json       ← pipeline run artifacts
.venv/ .lake/      ← build artifacts
*.pdf *.aux *.log  ← LaTeX build artifacts
anthropic_key.txt  ← API keys
openrouter_key.txt
```
