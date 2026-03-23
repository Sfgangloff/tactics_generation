# Session Brief — poly_norm · Condition D: Plan, LSP

**Tactic**: `poly_norm`
**Condition**: Milestone plan provided; LSP tools available.

---

## Setup

- Open a **fresh Claude Code session** in the project root
- The milestone plan **is** provided — work through it milestone by milestone
- You **may** use any LSP tools freely throughout
- **Do not** read any file in the repository other than the output file you are writing
  and the plan/spec provided below
- You may run `lake build` via Bash to check compilation
- Save each milestone as a separate file: `output.milestone1.lean`, `output.milestone2.lean`, etc.
- Keep a log of all LSP tool calls in `lean_lsp_log_poly_norm.md`

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
- You **may** use LSP tools freely (lean_goal, lean_diagnostic_messages,
  lean_leansearch, lean_loogle, lean_local_search, lean_multi_attempt,
  lean_hover_info, lean_completions, lean_state_search, lean_hammer_premise,
  lean_leanfinder, etc.).
- You may run `lake build` via Bash.
- Keep a running log of every LSP tool call (tool name, purpose, result) in
  `experiments/poly_norm/plan_with_lsp/lean_lsp_log_poly_norm.md`.

Save each milestone to its own file:
`experiments/poly_norm/plan_with_lsp/output.milestone1.lean`
`experiments/poly_norm/plan_with_lsp/output.milestone2.lean`
… and so on.

Keep the full cumulative test suite in each file.

Here is the specification:

[paste the full contents of experiments/poly_norm/poly_norm.spec.md]

Here is the milestone plan:

[paste the full contents of experiments/poly_norm/poly_norm.plan.md]

---

## What to record

After the session:
- Fill in `notes.md` using `experiments/notes_template.md`
- Save all milestone files
- Save `lean_lsp_log_poly_norm.md`

---

## Comparison baseline

| Condition | Plan | LSP | Status |
|-----------|------|-----|--------|
| A | No  | No  | not started |
| B | Yes | No  | not started |
| C | No  | Yes | not started |
| D | Yes | Yes | ← this session |
