#=
provable_count_test2.jl

Validation test that verifies the count_above function by comparing:
- count_a: Count computed by count_above (using Bell numbers)
- count_b: Count computed by explicit enumeration of all variable assignments

For each Catalan structure with n=6 implications:
1. Compute provable equivalence anti-chain
2. Get count using count_above (mathematical approach)
3. Enumerate all possible labelings with variables A, B, C
4. Check which labelings are actually provable
5. Compare counts - should match if algorithm is correct

Prints only shapes where counts disagree (indicating a bug).
If nothing prints, all tests pass!
=#

include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

catals = generate_catalan(6)
for (catal_i, catal) in enumerate(catals)
    shape = catalan_to_fml_shape(catal)
    eqac = provable_eqac(shape)

    # Method A: Count using Bell numbers
    count_a = count_above(eqac)[3]  # Index 3 = formulas with exactly 3 distinct variables

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
            push!(instances, tostr_with_labels(shape, vars))
        end
    end
    count_b = length(instances)

    # Report only mismatches
    if count_a != count_b
        println("$catal_i: $shape")
        println("count_above: $count_a")
        println("explicit: $count_b")
    end
end
