include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

for n in 0:9
    catals = generate_catalan(n)
    total = bell_zero
    for catal in catals
        shape = catalan_to_fml_shape(catal)
        #println("  ", shape)
        eqac = provable_eqac(shape)
        cnt = count_above(eqac)
        #println("  cnt: ", cnt)
        total += cnt
        #display(eqac.data)
        #println()
        #println()
    end
    println("$n arrows: $total provable")
end

