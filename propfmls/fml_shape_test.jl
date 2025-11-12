include("fml_shape.jl")

catals = generate_catalan(4)
display(catals)
println()
println()

for catal in catals
    println(catalan_to_fml_shape(catal))
end

