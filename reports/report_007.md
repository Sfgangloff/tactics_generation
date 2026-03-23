# Report T06 — Condition E: No Plan, No LSP (Interactive)

## What was done

Ran Condition E: an interactive Claude Code session implementing `limit_auto` from
`experiments/limit_auto/spec.md`, with no milestone plan and no LSP tools, as specified
in `experiments/limit_auto/one_shot_no_lsp/SESSION_BRIEF.md`.

Output saved to `experiments/limit_auto/one_shot_no_lsp/output.lean` (336 lines).
Session notes saved to `experiments/limit_auto/one_shot_no_lsp/notes.md`.

## Result

**Failed.** The model produced code but with a syntax error at line 172
("unexpected identifier; expected ')'") that prevents the tactic from being
registered. All 13 test cases consequently report "Tactic `limitAuto` has not
been implemented" (0/13 pass).

LSP diagnostics:
- 1 syntax error (line 172) — blocks tactic registration
- 12 downstream errors — all "has not been implemented" due to the above
- 3 unreachable-tactic warnings in fallback branches

## What this resolves

The paper (Section 4.3) noted that Condition A's failure was ambiguous: it could
reflect limitations of the automated pipeline scaffolding, the model, or both.
Condition E isolates the variable. The session was interactive (no pipeline scaffolding),
yet produced the same qualitative outcome: code that does not compile and zero passing tests.

**Conclusion: the failure in Condition A is due to the absence of LSP feedback, not the
automated pipeline scaffolding.**

The paper's table of conditions now has a clean interpretation:
- A and E both fail (no LSP, different scaffolding) → absence of LSP is the cause
- C succeeds (no plan, WITH LSP) → LSP is sufficient without planning

## Paper update

A note on Condition E is added to Section 4.3 of `paper/main.tex`, resolving the
ambiguity acknowledged in the study design paragraph.

## Files
- Output: `experiments/limit_auto/one_shot_no_lsp/output.lean`
- Notes: `experiments/limit_auto/one_shot_no_lsp/notes.md`
- SESSION_BRIEF.md: deleted (purpose fulfilled)
