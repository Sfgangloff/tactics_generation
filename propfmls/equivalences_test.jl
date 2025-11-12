include("equivalences.jl")

bell(15)
display(bell_precomputed)
println()
display([sum(a) for a in bell_precomputed])
println()
println()

eqs = Equivalence[]

for p1 in [(2,3), (2,4), (3,4)]
    for p2 in [(2,3), (2,4), (3,4)]
        eq = join(eq_pair(5,p1...), eq_pair(5,p2...))
        check(eq)
        push!(eqs, eq)
    end
end

eq_ac = make_EqAC(eqs)
display(eq_ac.data)
println()
println(count_above(eq_ac))
