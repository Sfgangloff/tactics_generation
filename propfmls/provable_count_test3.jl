#=
provable_count_test3.jl

Focused validation test for a specific Catalan structure (shape 125 of n=6).

Defines test_count_above function that:
1. Counts using count_above (mathematical approach with Bell numbers)
2. Counts by explicit enumeration with 3 variables (A, B, C)
3. Returns (match, count_mathematical, count_explicit)

Tests a single specific shape that may have been problematic in earlier testing.
Useful for debugging specific cases.

Output: (true, count, count) if test passes, (false, count1, count2) if mismatch
=#

include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

"""
    test_count_above(eqac) -> (Bool, Int, Int)

Validate count_above by comparing mathematical count vs explicit enumeration.

Returns tuple: (counts_match, mathematical_count, explicit_count)
"""
function test_count_above(eqac)
    # Method A: Count using Bell numbers
    count_a = count_above(eqac)[3]  # Index 3 = 3 distinct variables

    # Method B: Explicit enumeration
    instances = Set{String}()
    for eq in eqac.data
        cl = eq.num_classes
        # Try all possible assignments of 3 values to cl equivalence classes
        for i in 0:3^cl-1
            vars_int = Int[]
            i0 = i
            # Assign variables according to equivalence relation
            for (j,x) in enumerate(eq.data)
                if j == x  # Class representative
                    push!(vars_int, i%3+1)
                    i ÷= 3
                else  # Non-representative: inherit from representative
                    push!(vars_int, vars_int[eq.data[x]])
                end
            end
            @assert i == 0

            # Verify that variables appear in canonical order (A before B before C)
            last_var = 0
            for x in Iterators.reverse(vars_int)
                if last_var+1 == x
                    last_var = x
                elseif last_var < x
                    break
                end
            end
            if last_var != 3 continue end  # Skip if not using all 3 variables

            vars = [['A','B','C'][x] for x in vars_int]
            push!(instances, String(vars))
        end
    end
    count_b = length(instances)
    return count_a == count_b, count_a, count_b
end

# Test specific potentially problematic case
catals = generate_catalan(6)
catal = catals[125]  # Shape 125 of n=6

shape = catalan_to_fml_shape(catal)
eqac = provable_eqac(shape)
println(test_count_above(eqac))
