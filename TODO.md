# TODO — Paper Submission Checklist

Items marked **[USER]** require a decision or action from the researcher.
Items marked **[DONE]** are complete; see `reports/` for details.

---

## Paper content

- [x] **T01** — Add quantitative comparison table to paper (LOC, tests, milestones, LSP calls per condition) ✓ `reports/report_001.md`
- [x] **T02** — Resolve `\comment{}` on file paths → replace with repo URL placeholder ✓ `reports/report_002.md`
- [x] **T03** — Condense pilot section to ~1 page for ITP short paper ✓ `reports/report_003.md`
- [x] **T04** — Writing polish: tighten abstract, sharpen key claim in intro ✓ `reports/report_004.md`
- [ ] **T05** — Switch LaTeX class to LNCS (`llncs`) for ITP formatting **[USER: add author names/affiliations]**
- [ ] **T06 [USER]** — Decide whether to run Condition A interactively (Claude Code, no plan, no LSP) to disambiguate failure cause
- [ ] **T07 [USER]** — Run full 2×2 study on `decide_list_theory` (have spec + plan already)
- [ ] **T08 [USER]** — Spec comparison experiment: researcher-written vs model-generated spec on same tactic
- [ ] **T09 [USER]** — Analogical prompting experiment: prompt model to recall similar tactic before generating
- [ ] **T10 [USER]** — Create Zenodo DOI / stable repo archive; replace file-path refs with URL in camera-ready

## Pipeline improvements

- [x] **T11** — Add error-analysis step to self-correction loop in `pipeline/generator.py` (Boosting-of-Thoughts style) ✓ `reports/report_005.md`

## Repository / infrastructure

- [ ] **T12 [USER]** — Add `CITATION.cff` once author list is finalized
- [ ] **T13** — Verify `lake build` passes cleanly on CI (check GitHub Actions)

---

*Reports for completed items are in `reports/`.*
