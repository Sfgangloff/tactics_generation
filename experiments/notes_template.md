# Session Notes Template

Fill in one copy of this file per experimental session (one condition × one tactic).
Save it as `notes.md` inside the condition directory immediately after the session.
Takes ≤ 15 minutes to fill.

---

## Identity

| Field | Value |
|-------|-------|
| Tactic | _(e.g. `nonzero`)_ |
| Condition | _(A / B / C / D)_ |
| Plan | _(Yes / No)_ |
| LSP tools | _(Yes / No)_ |
| Date | _(YYYY-MM-DD)_ |

---

## Outcome

| Field | Value |
|-------|-------|
| Compiled? | _(Yes / No)_ |
| Tests passing / total | _(e.g. 18 / 25)_ |
| Milestones completed / planned | _(e.g. 10 / 10, or — if no plan)_ |
| First milestone that compiled | _(e.g. M2, or — if no milestones)_ |

---

## Effort metrics

| Field | Value |
|-------|-------|
| LOC — implementation body (excl. tests) | _(count)_ |
| LOC — test suite | _(count)_ |
| `lake build` calls | _(count)_ |
| Repair cycles (error → fix iterations) | _(count; one cycle = one round of edits in response to a compiler error)_ |

---

## LSP tool usage  _(Condition C and D only; leave blank for A and B)_

| Tool | Calls |
|------|-------|
| `lean_diagnostic_messages` | |
| `lean_goal` | |
| `lean_leansearch` | |
| `lean_loogle` | |
| `lean_leanfinder` | |
| `lean_local_search` | |
| `lean_multi_attempt` | |
| `lean_hover_info` | |
| `lean_state_search` | |
| `lean_hammer_premise` | |
| `lean_completions` | |
| **Total** | |

---

## Per-milestone summary  _(Condition B and D only; omit for A and C)_

| Milestone | Tests passing | Repair cycles | LSP calls |
|-----------|--------------|---------------|-----------|
| M1 | | | |
| M2 | | | |
| M3 | | | |
| … | | | |

---

## Notable failures and errors

List the 1–3 most significant errors encountered, with a one-line description of the fix:

1. _(Milestone / line — error summary — fix applied)_
2.
3.

---

## Free observations

_(Optional. Anything not captured above: surprising lemma names, architectural choices,
places where planning helped/didn't help, etc. Keep to ≤ 5 bullet points.)_

-
