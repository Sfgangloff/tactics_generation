# Session Brief — nonzero · Condition C: No Plan, LSP

**Tactic**: `nonzero`
**Condition**: No milestone plan; LSP tools available.

---

## Setup

- Open a **fresh Claude Code session** in the project root
- **No plan is provided** — the model must devise its own approach
- You **may** use any LSP tools freely:
  `lean_goal`, `lean_diagnostic_messages`, `lean_leansearch`, `lean_loogle`,
  `lean_local_search`, `lean_multi_attempt`, `lean_hover_info`,
  `lean_completions`, `lean_state_search`, `lean_hammer_premise`,
  `lean_leanfinder`, etc.
- **Do not** read any file in the repository other than the output file you are writing
- You may run `lake build` via Bash to check compilation

---

## Prompt to give the model

Paste the following as your first message:

---

I want you to implement a Lean 4 tactic called `nonzero` following the specification
below.

Constraints:
- **No milestone plan is provided** — decide your own implementation approach.
- Do not read any file in the repository. All information you need is in this prompt.
  Only write to the output file.
- You **may** use LSP tools freely (lean_goal, lean_diagnostic_messages,
  lean_leansearch, lean_loogle, lean_local_search, lean_multi_attempt,
  lean_hover_info, lean_completions, lean_state_search, lean_hammer_premise,
  lean_leanfinder, etc.).
- You may run `lake build` via Bash.

Save all output to a single file:
`experiments/nonzero/no_plan_with_lsp/output.lean`

Keep the full test suite in the file at all times.

Here is the specification:

[paste the full contents of experiments/nonzero/nonzero.spec.md]

---

## What to record

After the session, fill in `notes.md` using `experiments/notes_template.md`.
Save `output.lean` (even if it does not compile fully).

---

## Comparison baseline

| Condition | Plan | LSP | Status |
|-----------|------|-----|--------|
| A | No  | No  | not started |
| B | Yes | No  | not started |
| C | No  | Yes | ← this session |
| D | Yes | Yes | not started |
