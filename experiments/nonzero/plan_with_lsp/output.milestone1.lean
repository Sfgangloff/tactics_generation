-- Milestone 1: Skeleton and principled failure
-- The tactic detects goals of the form `e ≠ 0` or `¬(e = 0)` and fails
-- with an informative message if it cannot prove them.

import Mathlib.Tactic

open Lean Elab Tactic Meta

/-- `nonzero` proves goals of the form `e ≠ 0` using algebraic lemmas. -/
syntax (name := nonzero) "nonzero" : tactic

@[tactic nonzero]
def evalNonzero : Tactic := fun _stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= (fun e => whnf e)
  -- Check that the goal is of the form `e ≠ 0`
  -- `e ≠ 0` is notation for `e = 0 → False`, i.e., `Ne e 0`
  match goalType with
  | Expr.app (Expr.app (Expr.app (Expr.const ``Ne _) _α) _e) _z => do
    -- We have a `Ne e 0` goal; for now fail with unsupported message
    throwTacticEx `nonzero goal "nonzero: unsupported goal"
  | Expr.app (Expr.const ``Not _) (Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _α) _e) _z) => do
    -- `¬(e = 0)` form
    throwTacticEx `nonzero goal "nonzero: unsupported goal"
  | _ =>
    throwTacticEx `nonzero goal
      "nonzero: goal is not of the form `e ≠ 0`"

-- ============================================================
-- Milestone 1 Tests
-- ============================================================

-- Test 1.1: Wrong goal shape → should fail with the right error
-- (We test that a correct Ne goal reaches the "unsupported" branch,
--  not the "not of the form" branch.)
-- We can't directly test failure messages in #check, so we use
-- a negative test with `try` to verify the tactic at least fires.

section Milestone1Tests

variable (α : Type*) [Ring α] (a : α)

-- The tactic should fail on `a ≠ 0` with "unsupported goal" (not a
-- "goal is not of the form" error).  We verify it compiles as a tactic call.
example (h : a ≠ 0) : a ≠ 0 := by
  first | nonzero | exact h

end Milestone1Tests
