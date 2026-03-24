#=
fml_shape_test.jl

Test script for Catalan structure generation and formula shape conversion.

Tests:
1. Generates all Catalan structures (Dyck paths) for n=4 implications
2. Displays raw Catalan representations
3. Converts each to FmlShape and prints in human-readable format

Expected output: 14 different formula shapes (the 4th Catalan number)
=#

include("fml_shape.jl")

# Generate all Catalan structures for n=4
catals = generate_catalan(4)
display(catals)
println()
println()

# Convert each Catalan structure to formula shape and display
for catal in catals
    println(catalan_to_fml_shape(catal))
end

