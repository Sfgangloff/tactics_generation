# Report T02 — Resolve `\comment{}` annotations

## What was done

Removed all three remaining `\comment{}` margin annotations from `paper/main.tex`:

1. **Lines 115–120** (intro): "how to evaluate differences / don't restrict to limit_auto"
   — Removed. The quantitative table (T01) addresses the evaluation question.
   The generalization question is addressed in Future Work.

2. **Lines 530–531** (§4.3 implementation): "should we point at file paths or repo URL?"
   — Resolved in favor of the repo URL. Replaced the file-path reference with
   `\url{https://github.com/Sfgangloff/tactics_generation}` + path.

3. **Line 229** (pilot section): "is this section too detailed?"
   — Addressed by T03 (condensing the pilot section).

## Why

All `\comment{}` annotations were open editorial questions. Removing them cleans
up the draft and replaces each with a concrete decision. The paper now compiles
without any margin notes.
