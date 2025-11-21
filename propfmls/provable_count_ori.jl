#=
provable_count_ori.jl

Original/reference implementation of the provability analysis algorithm.

This is a simpler version without the cycle detection optimization found in
provable_count.jl. It may be less efficient but is easier to understand
and serves as a reference for correctness.

Main differences from provable_count.jl:
1. No cycle detection (may not terminate on certain formulas)
2. Simpler hypothesis management (just filters out current hypothesis)
3. No recent_goals tracking

Use this for understanding the core algorithm or for comparison testing.
For production use, prefer provable_count.jl which handles edge cases better.
=#

"""
    provable_eqac(shape :: FmlShape) -> EqAC

Reference implementation of provability analysis without cycle detection.

Simpler but potentially less robust than the optimized version in provable_count.jl.
"""
function provable_eqac(shape :: FmlShape)
    provable_eqac(shape, length(shape.data), 1, Int[])
end

"""
    provable_eqac(shape, n, root, hyps) -> EqAC

Recursive backward proof search (reference implementation).

# Algorithm
1. Add root's assumptions to available hypotheses
2. Try each hypothesis h:
   a. Unify root with h
   b. Recursively prove all premises of h
   c. Remove h from hypotheses to avoid immediate reuse
3. Union all solutions

# Note
This version lacks cycle detection and may not terminate on certain formulas.
Use provable_count.jl for production code.
"""
function provable_eqac(shape :: FmlShape, n :: Int, root :: Int, hyps :: Vector{Int})
    hyps = vcat(hyps, shape.data[root])  # Add root's assumptions
    res = EqAC(Equivalence[])

    for h in hyps
        hyps2 = filter((h2 -> h2 != h), hyps)  # Remove current hypothesis
        cur_sol = EqAC([eq_pair(n, root, h)])  # Unify root with hypothesis

        # Prove all premises of h
        for subgoal in shape.data[h]
            cur_sol = intersect(cur_sol, provable_eqac(shape, n, subgoal, hyps2))
        end

        res = union(res, cur_sol)
    end
    return res
end
