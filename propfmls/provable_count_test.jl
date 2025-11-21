#=
provable_count_test.jl

Test script that counts total provable formulas for each n (number of implications).

For n=0 to n=9:
- Generates all Catalan structures (formula shapes)
- Determines which variable assignments make each shape provable
- Counts total provable formulas (sum across all shapes)
- Reports statistics: "n arrows: [count distribution] provable"

This validates that the provability analysis and counting works correctly
across all formula sizes.
=#

include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

for n in 0:9
    catals = generate_catalan(n)
    total = bell_zero
    for catal in catals
        shape = catalan_to_fml_shape(catal)
        eqac = provable_eqac(shape)
        cnt = count_above(eqac)
        total += cnt
    end
    println("$n arrows: $total provable")
end

