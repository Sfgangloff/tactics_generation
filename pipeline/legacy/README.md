# Legacy Pipeline Material

This directory contains earlier iterations of the pipeline, kept for historical context.
None of this code is used by the current pipeline (`pipeline/*.py`).

---

## `scripts/` — First-generation repair loop

These scripts predate `generator.py` and `validator.py`. They implemented an
iterative compile-and-repair loop using the Claude Agent SDK directly.

| File | Description |
|------|-------------|
| `fix_lean.py` | Original repair loop: calls `lake env lean`, feeds errors back to LLM |
| `fix_tactic_file.py` | Variant focused on tactic files specifically |
| `fix_tactic_focused.py` | More focused tactic repair (single-file, one-shot correction) |
| `README_fix_tactic.md` | Notes on the repair approach |

**Relationship to paper**: These scripts implement the self-correction loop used in
Conditions A and B of the 2×2 study. The current `generator.py` generalises this
approach with cleaner abstractions.

---

## `prompts/` — Earlier prompt templates

Two prompts from this era are still relevant:

| File | Description |
|------|-------------|
| `metaprogramming_tutorial.txt` | Lean 4 tactic programming guide injected into generation prompts. Based on the [lean-tactic-programming-guide](https://github.com/mirefek/lean-tactic-programming-guide). |
| `fix_tactic_system.txt` | System prompt for the repair stage, tactic-specific variant |

---

## `agents_search/` — Pre-LSP Lean search agent

A GPT-4o-mini powered semantic search tool for the Lean 4 Batteries library.
Built before the LSP tool approach used in Conditions C and D.

**What it does**: Given a natural language description (e.g., "multiply two naturals"),
finds relevant Lean 4 definitions, returns their signatures, import paths, and usage hints.

**Architecture**:
- `src/lean_indexer.py` — scrapes Lean source files to build a definition index
- `src/search_agent.py` — LLM-powered query analysis and ranking
- `src/searcher.py` — vector-style search over the indexed definitions
- `src/import_resolver.py` — resolves which `import` statement is needed
- `data/lean_index.json`, `data/enriched_lean_index.json` — pre-built indexes

**Relationship to paper**: This agent was a precursor to the LSP tools (`lean_leansearch`,
`lean_loogle`, `lean_local_search`) used in Conditions C and D. The LSP approach
superseded it because it queries live Mathlib rather than a static pre-built index,
and therefore reflects current lemma names and deprecations.
