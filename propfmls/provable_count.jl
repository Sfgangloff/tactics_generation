#=
provable_count.jl

Implements backward proof search to determine which variable assignments
make a propositional formula provable in natural deduction.

The main algorithm performs backward chaining from a goal, trying to
match it against available hypotheses. Returns an anti-chain of equivalence
relations representing all provable variable assignments.
=#

"""
    provable_eqac(shape :: FmlShape) -> EqAC

Determine all variable assignments that make the formula shape provable.

# Algorithm
Performs backward proof search from the root goal (node 1) with its
direct assumptions as initial hypotheses.

# Arguments
- `shape`: Formula shape to analyze

# Returns
EqAC (anti-chain) representing all equivalence relations under which
the formula is provable. Empty anti-chain means the formula is unprovable
for all distinct variable assignments.

# Example
```julia
# Shape: (A → B) → A
# Unprovable when A ≠ B (cannot derive A from A→B alone)
# Provable when A = B (becomes (A → A) → A, which is trivial)
```
"""
function provable_eqac(shape :: FmlShape)
    provable_eqac(shape, length(shape.data), 1, shape.data[1], Int[])
end

"""
    provable_eqac(shape, n, goal, hyps, recent_goals) -> EqAC

Recursive backward proof search with loop detection.

# Algorithm (Backward Chaining)
To prove goal with hypotheses hyps:
1. For each hypothesis h in hyps:
   a. If h matches goal (considering variable unification), record solution
   b. If h is an implication, recursively prove its premises
   c. Combine with previous premises using intersection (all must hold)
2. Combine solutions from different hypotheses using union (any can work)

# Arguments
- `shape`: Formula shape being analyzed
- `n`: Total number of nodes in the formula
- `goal`: Current goal node to prove
- `hyps`: Available hypothesis nodes (assumptions in scope)
- `recent_goals`: Stack of recent goals for cycle detection

# Returns
EqAC representing all equivalences making this goal provable from these hypotheses.

# Loop Detection
If we encounter the same goal with the same hypotheses, we have a non-productive
cycle and skip this branch to avoid infinite recursion.

# Example
```julia
# Goal: node 1, Hyps: [node 2]
# If node 2 has assumptions [node 3], we:
# - Try to unify goal with node 2: requires node 1 ≡ node 2
# - Recursively prove node 3 with updated hypotheses
# - Intersect results (both unification AND subproof must succeed)
```
"""
function provable_eqac(shape :: FmlShape, n :: Int, goal :: Int, hyps :: Vector{Int}, recent_goals :: Vector{Int})
    # Track goal history for cycle detection
    recent_goals = copy(recent_goals)
    push!(recent_goals, goal)
    res = EqAC(Equivalence[])  # Start with empty solution set

    # Try each hypothesis as a potential proof step
    for h in hyps
        # Prepare to prove all subgoals of h (its assumptions/premises)
        hyps2_all = Vector{Int}[]
        repetitive = false

        for subgoal in shape.data[h]
            # Collect new hypotheses: existing hyps + assumptions of subgoal
            hyps2 = copy(hyps)
            for a in shape.data[subgoal]
                if a ∉ hyps2
                    push!(hyps2, a)
                end
            end

            # Cycle detection: same goal with same hypotheses = infinite loop
            if length(hyps2) == length(hyps) && subgoal in recent_goals
                repetitive = true
                break
            end
            push!(hyps2_all, hyps2)
        end
        if repetitive continue end  # Skip this branch to avoid infinite recursion

        # Solution requires: goal ≡ h (unify goal with hypothesis)
        cur_sol = EqAC([eq_pair(n, goal, h)])

        # Also requires: all premises of h must be provable (intersection)
        for (subgoal, hyps2) in zip(shape.data[h], hyps2_all)
            # Reset recent_goals if we gained new hypotheses (breaks cycle)
            rg2 = if length(hyps2) == length(hyps)
                recent_goals  # No new hypotheses: continue cycle detection
            else
                Int[]  # New hypotheses available: reset cycle detection
            end
            # Recursively prove subgoal and intersect with current solution
            cur_sol = intersect(cur_sol, provable_eqac(shape, n, subgoal, hyps2, rg2))
        end

        # Combine with solutions from other hypotheses (union: any can work)
        res = union(res, cur_sol)
    end

    return res
end

