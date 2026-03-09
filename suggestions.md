# Suggestions for Paper Submission

Target venues (in rough order of deadline proximity):
- **NeurIPS workshop** (e.g. Math-AI, AITP, or similar) — shorter, ML-oriented framing
- **ITP 2025/2026 short paper** — 8 pages LNCS, formal-methods audience
- **AITP workshop** — dedicated AI for theorem proving, smaller community but high fit

---

## 1. Resolve open `\comment{}` annotations in the paper

Four margin comments remain open in `paper/main.tex`:

- **Line 115–120**: How to evaluate the difference between conditions quantitatively, and whether to restrict to `limit_auto` or generalize. This is the biggest open question — see §3 below.
- **Line 229**: Whether the pilot section is too detailed. Decision needed on how much space to give it vs the main study.
- **Line 508–509**: Whether to point to file paths or a repository URL in the final paper. Answer: use a GitHub URL + commit hash (or a Zenodo DOI) for camera-ready.

---

## 2. Evaluation: add a quantitative comparison table

Currently the 2×2 study is purely qualitative (narrative descriptions of each condition).
For a credible conference submission, you need at least a minimal quantitative table.
Suggested metrics to add for each condition:

| Condition | Compiles? | Tests pass | Repair rounds | LOC | LSP calls |
|-----------|-----------|------------|---------------|-----|-----------|
| A         | No        | 0/N        | ~4 (budget)   | 0   | 0         |
| B         | Yes       | k/N        | ?             | ?   | 0         |
| C         | Yes       | N/N        | ?             | ?   | ?         |
| D         | Yes       | N/N        | 0 (per milestone) | ? | 22 (from lsp_log.md) |

For conditions B–D: count the actual repair rounds, lines of code in the final tactic,
and number of tests. Condition D LSP call counts are already logged in `lsp_log.md`.
For B and C you'd need to check the milestone/output files directly.

---

## 3. Generalizability: run the study on at least one more tactic

The biggest weakness of the current paper is that the 2×2 study is a single-tactic case
study. The `decide_list_theory` tactic (Condition D only) is a start but not a full 2×2.

**Option A (recommended):** Run all four conditions on `decide_list_theory`, which you
have the spec and plan for already. This gives a second data point and lets you check
whether the Condition A/B/C/D ordering holds on a different tactic.

**Option B (lighter):** Run just Condition A (pipeline) on a few of the 12 draft specs
in `experiments/other_tactics/specs/` and report success/failure. Even a batch result
("pipeline succeeded on X/12 specs from a single API call") strengthens the claim.

---

## 4. Disambiguate Condition A's failure

Currently the Condition A failure is explicitly acknowledged as ambiguous (pipeline
scaffolding vs. model). To resolve this:

Run Condition A interactively in Claude Code (same setup as B/C/D, but without a plan
and without LSP tools). If it also fails, the failure is attributable to the absence
of scaffolding rather than the automated pipeline. This is a one-session experiment.

---

## 5. Pilot section: decide on length

The pilot section is now detailed (three approaches, file-level breakdown). For an 8-page
ITP short paper this is likely too long. Two options:

- **Condense to ~1 page**: keep only the three-approach narrative and the key insight;
  drop the file-level details (readers can find them in the repo).
- **Keep detail for a workshop paper**: NeurIPS workshop papers typically allow 4–8 pages
  with more flexible structure; the detail could be kept there.

---

## 6. Venue-specific formatting

The current draft uses `article` class with 1-inch margins. Both ITP and most NeurIPS
workshops require specific styles:

- **ITP** (Springer LNCS): `llncs` class, 12pt, specific author/affiliation format,
  8 pages + references. Bibliography must be `splncs04.bst`.
- **NeurIPS workshop**: usually a custom `neurips_YYYY` class, 4–8 pages.
- **AITP**: extended abstract format, 4 pages.

Switch the LaTeX class early — page limits look very different in LNCS format and you
will need to cut material.

---

## 7. Repository archival for submission

Before camera-ready:
- Create a **Zenodo DOI** or use the GitHub archive URL + commit hash so the paper can
  cite a stable version of the repo.
- Replace all file-path references in the paper with the archived repo URL + path.
- Add `CITATION.cff` or equivalent to the repo root.
- Ensure `lake build` passes cleanly (CI workflow is now in place).

---

## 8. Writing polish (lower priority, do last)

- **Abstract**: tighten to 150 words. Currently it may be over the LNCS limit.
- **Title**: "An Empirical Study" is accurate but a bit generic. Consider whether the
  focus should be on the LSP-vs-plan finding specifically.
- **Related work**: check that DeepSeek-Prover, AlphaProof, Harmonic citations are
  formatted correctly and that no major 2024–2025 LLM+Lean paper is missing.
- **Key claim**: make the main takeaway explicit and early — currently it is implicit.
  Suggested: "LSP access to the live compiler matters more than planning alone."

---

## 9. Analysis of `advanced_suggestions.md` — which suggestions are worth pursuing

The AI-generated suggestions in `advanced_suggestions.md` compare our work to the
prompting-strategies literature. Here is an assessment of each, and a plan for which
to act on.

### Already done (in the current paper draft)

The following connections have been made explicit in the Related Work section:

- **Milestone planning ≈ Least-to-Most / Plan-and-Solve Prompting**: added citations to
  Zhou et al. 2022 (arXiv:2205.10625) and Wang et al. 2023 (arXiv:2305.04091).
- **Specification-first ≈ Problem Elaboration Prompting**: cited Liao et al. 2024
  (arXiv:2402.15764, "Look Before You Leap").
- **Self-correction loop ≈ Progressive-Hint Prompting**: cited Zheng et al. 2023
  (arXiv:2304.09797).
- **LSP + plan ≈ Proposer-Verifier-Reporter (Cumulative Reasoning)**: cited Zhang et al.
  2023 (arXiv:2308.04371); also framed this in the Related Work discussion.
- **Spec-first + external verifier ≈ SatLM**: cited Ye et al. 2023 (arXiv:2305.09656).

### Actionable as new experiments (medium-term)

**Analogical prompting before tactic generation** *(Large Language Models as Analogical
Reasoners, arXiv:2310.01714; Thought Propagation, arXiv:2310.03965)*

The suggestion: before generating a new tactic, prompt the model to recall a known
similar Lean tactic (e.g. `ring`, `norm_num`, `decide`) and describe how it works,
then generate the target tactic by analogy.

**Plan**: Run one new tactic generation session (e.g. one of the 12 draft specs) using
an analogical prompt prefix. Compare output quality against a non-analogical run.
If successful, this becomes a fifth condition in the study design.
Cost: one session, ~1 hour.

**Formal comparison of researcher-written vs. model-generated specifications**
*(Self-improvement by RL Contemplation, arXiv:2305.14483; bridges Approaches 2 and 3
in the pilot)*

Currently the pilot shows qualitatively that researcher-written specs (Approach 3)
outperform model-inferred specs (Approach 2), but this is not systematically evaluated.

**Plan**: For the same tactic (e.g. `decide_list_theory`), generate the spec two ways:
(a) pipeline `analyze_request` stage (model-generated), (b) researcher-written.
Then implement under the same condition (D: plan + LSP) and compare the resulting tactics
on test pass rate, LOC, and number of LSP calls needed. This directly addresses the
open `\comment{}` on line 115 of the paper about how to evaluate condition differences.
Cost: one additional session, moderate.

**Better self-correction via explicit error analysis** *(Boosting of Thoughts,
arXiv:2402.11140; Recursive Decomposition with Dependencies, arXiv:2505.02576)*

The current Condition A/B self-correction loop feeds raw compiler errors back. BoT
suggests also asking the model to *explain* the error and *revise the strategy*, not
just the code, before the next attempt.

**Plan**: Modify `pipeline/generator.py`'s repair loop to add an intermediate "error
analysis" step: after receiving compiler errors, prompt the model to explain what went
wrong and what strategy change is needed, then generate the repair. Compare repair
convergence rate against the current loop on the batch of 12 specs.
Cost: pipeline modification (~2h) + one batch run.

### Low priority / longer-term (not for current submission)

- **Concise and Organized Perception** (arXiv:2310.03309): filter/organize Lean context
  before prompting. Could help when specs become long. Not urgent given current spec sizes.
- **Recursive Decomposition for large tactics** (arXiv:2505.02576): relevant if tactics
  grow beyond ~300 LOC. Not currently needed.
- **MetaLadder** (arXiv:2503.14891): structured analogical transfer. More complex to
  implement than basic analogical prompting; defer until the simpler version is tested.
- **Successive Prompting** (arXiv:2212.04092), **Decomposed Prompting** (arXiv:2210.02406):
  largely subsumed by Least-to-Most + Plan-and-Solve in what they add to the paper.

### Summary priority order

| Priority | Action | Effort |
|----------|--------|--------|
| Now (done) | Cite 5 prompting papers in Related Work | ✓ done |
| Short-term | Quantitative table (§2 above) | Low |
| Short-term | Spec comparison experiment (researcher vs model) | Medium |
| Medium | Analogical prompting experiment | Medium |
| Medium | Better self-correction loop in pipeline | Medium |
| Longer-term | Full 2×2 on second tactic | High |
