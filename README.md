# Lean 4 Tactic Generation — Empirical Study

This repository accompanies the paper:

> **Generating Lean 4 Tactics from User Specifications: An Empirical Study of LLM-Assisted Metaprogramming Strategies**

We study whether large language models can generate working Lean 4 tactics from
informal user specifications, and which scaffolding strategies — formal specifications,
milestone plans, live LSP feedback — make generation reliable.

---

## Navigating the Repository

### I want to read the paper or study plan

```
paper/
  main.tex          ← LaTeX draft
  paper_plan.md     ← section outline, evidence table, key claims
```

### I want to understand the experiments

```
experiments/
  intuitionistic_pilot/     ← Section 3: pilot experiment (propositional logic tactic)
  limit_auto/               ← Section 4: main 2×2 study
  other_tactics/            ← Section 7: future work (decide_list_theory + 12 specs)
```

### I want to run the pipeline

The pipeline prepares interactive Claude Code sessions. Given an
informal tactic description, it produces two artefacts:

1. **Specification** (`.spec.md`) — a structured analysis of the tactic: name, scope,
   mathematical characterisation, algorithm, success criteria, edge cases, and dependencies.
2. **Milestone plan** (`.plan.md`) — an incremental refinement plan with 8–12 milestones.
   Each milestone names the new capability, gives concrete Lean 4 example goals, cites
   relevant Mathlib lemmas, and describes the implementation step. The researcher then
   works through the plan milestone by milestone inside Claude Code with live LSP access.

The pipeline makes two LLM calls — one per artefact — and writes both files to `output/`.
No Lean compilation happens; all interactive work is done in Claude Code.

```bash
# Setup
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
export ANTHROPIC_API_KEY="your-key"   # or OPENAI_API_KEY, OPENROUTER_API_KEY

# Single tactic
python pipeline/main.py "A tactic that proves nonzero goals"
python pipeline/main.py --provider openrouter --model google/gemini-pro "..."
python pipeline/main.py -f request.txt

# Batch mode (from specifications.json)
python pipeline/main.py --batch pipeline/specifications.json
python pipeline/main.py --batch pipeline/specifications.json --only Tendsto Nonzero
python pipeline/main.py --batch pipeline/specifications.json --skip RewriteAC
```

Output files are written to `output/<tactic_name>.spec.md` and `output/<tactic_name>.plan.md`.

See [`pipeline/README.md`](pipeline/README.md) for architecture details.

---

## Repository Structure

```
.
├── README.md               ← this file
├── CLAUDE.md               ← project instructions for Claude Code
│
├── paper/
│   ├── main.tex            ← paper draft (LaTeX, ITP short paper)
│   └── paper_plan.md       ← section outline and evidence table
│
├── experiments/
│   ├── intuitionistic_pilot/
│   │   ├── README.md
│   │   ├── *.lean / *.spec.md        ← spec-first tactic versions (pilot outcome)
│   │   ├── gpt5_iterations/          ← 13 GPT-5 iterations (iterative approach)
│   │   └── formula_enumeration/      ← Julia: propositional formula enumeration (background)
│   │
│   ├── limit_auto/              ← 2×2 study (main paper contribution)
│   │   ├── spec.md              ← shared specification for all 4 conditions
│   │   ├── plan.md              ← milestone plan (used in Conditions B and D)
│   │   ├── README.md            ← study design and condition descriptions
│   │   ├── one_shot_no_lsp/     ← Condition A: no plan, no LSP (baseline)
│   │   ├── plan_without_lsp/    ← Condition B: plan, no LSP
│   │   ├── one_shot_with_lsp/   ← Condition C: no plan, with LSP
│   │   └── plan_with_lsp/       ← Condition D: plan + LSP (best)
│   │
│   └── other_tactics/
│       ├── README.md
│       ├── decide_list_theory/  ← second complete tactic (LSP-guided)
│       ├── specs/               ← 12 drafted specifications
│       └── plans/               ← milestone plans for each spec (pipeline output)
│
├── pipeline/
│   ├── README.md
│   ├── main.py             ← CLI entry point
│   ├── specifications.json ← tactic descriptions for batch mode
│   ├── config.py           ← configuration (provider, model, output dir)
│   ├── generator.py        ← pipeline orchestrator (spec + plan generation)
│   ├── models/             ← LLM provider wrappers (Anthropic, OpenAI, OpenRouter)
│   ├── prompts/            ← prompt templates (analyze_request, generate_plan, split_specifications)
│   └── legacy/             ← earlier approaches (see pipeline/legacy/README.md)
│
├── output/                 ← pipeline output: *.spec.md and *.plan.md files
├── requirements.txt        ← Python dependencies (anthropic, openai)
├── lakefile.toml           ← Lean 4 project configuration (Mathlib dependency)
├── lean-toolchain          ← pinned Lean version
└── Main.lean               ← minimal Lean entry point (required by Lake)
```

---

## The 2×2 Study Design

The central experiment studies four strategies for generating the `limit_auto` tactic
(which proves `Tendsto f F G` goals in Lean 4 / Mathlib):

|                    | No milestone plan        | With milestone plan      |
|--------------------|--------------------------|--------------------------|
| **No LSP tools**   | A: raw one-shot (empty)  | B: plan, no LSP          |
| **With LSP tools** | C: one-shot + LSP        | D: plan + LSP (best)     |

- **Condition A**: single API call, self-correction loop → produces nothing usable
- **Condition B**: structured plan, API calls with self-correction → compiles, tests fail (wrong Mathlib API names)
- **Condition C**: one-shot in Claude Code with live LSP → zero errors, all tests pass
- **Condition D**: 9-milestone plan with live LSP at each step → zero errors, richest test suite

**Key finding**: LSP access to the live Lean compiler is more valuable than planning alone
(C dominates B). Combined, they give the best result (D).

---

## Lean Setup

```bash
# Install Lean toolchain (see https://leanprover.github.io/lean4/doc/setup.html)
lake update
lake build
```

The project requires Mathlib (pinned via `lake-manifest.json`). Build time for Mathlib
is ~30 minutes on first run; subsequent builds are cached.
