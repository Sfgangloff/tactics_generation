#=
equivalences_test.jl

Test script for equivalence relation operations and Bell number computation.

Tests:
1. Bell triangle computation up to n=15
2. Displays Bell numbers (sum of each row)
3. Tests equivalence join operations on pairs
4. Tests anti-chain construction and counting
=#

include("equivalences.jl")

# Test Bell number computation
bell(15)
display(bell_precomputed)
println()
display([sum(a) for a in bell_precomputed])
println()
println()

# Test equivalence operations: join pairs and build anti-chain
eqs = Equivalence[]

for p1 in [(2,3), (2,4), (3,4)]
    for p2 in [(2,3), (2,4), (3,4)]
        eq = join(eq_pair(5,p1...), eq_pair(5,p2...))
        check(eq)  # Verify invariants
        push!(eqs, eq)
    end
end

# Test anti-chain construction
eq_ac = make_EqAC(eqs)
display(eq_ac.data)
println()
println(count_above(eq_ac))
