# Session Brief — poly_norm · Condition B: Plan, No LSP

**Tactic**: `poly_norm`
**Condition**: Milestone plan provided; no LSP tools.

---

## Setup

- Open a **fresh Claude Code session** in the project root
- The milestone plan **is** provided — work through it milestone by milestone
- **Do not** use any LSP tools
- **Do not** read any file in the repository other than the output file you are writing
  and the plan/spec provided below
- You may run `lake build` via Bash to check compilation
- Save each milestone as a separate file: `output.milestone1.lean`, `output.milestone2.lean`, etc.

---

## Prompt to give the model

Paste the following as your first message:

---

I want you to implement a Lean 4 tactic called `poly_norm` following the specification
and milestone plan below.

Constraints:
- Work through the milestones **one at a time**. For each milestone, produce a complete
  Lean file that compiles (or attempt repair if it does not), then move to the next.
- Do not read any file in the repository. All information you need is in this prompt.
- Do **not** use any LSP tools (no `lean_goal`, `lean_diagnostic_messages`, etc.).
- You may run `lake build` via Bash to check compilation.

Save each milestone to its own file:
`experiments/poly_norm/plan_without_lsp/output.milestone1.lean`
`experiments/poly_norm/plan_without_lsp/output.milestone2.lean`
… and so on.

Keep the full cumulative test suite in each file.

Here is the specification:

[paste the full contents of experiments/poly_norm/poly_norm.spec.md]

Here is the milestone plan:

[paste the full contents of experiments/poly_norm/poly_norm.plan.md]

---

## What to record

After the session, fill in `notes.md` using `experiments/notes_template.md`.
Save all milestone files (even those that do not compile).

---

## Comparison baseline

| Condition | Plan | LSP | Status |
|-----------|------|-----|--------|
| A | No  | No  | not started |
| B | Yes | No  | ← this session |
| C | No  | Yes | not started |
| D | Yes | Yes | not started |
