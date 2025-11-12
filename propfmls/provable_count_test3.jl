include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

function test_count_above(eqac)
    count_a = count_above(eqac)[3]
    instances = Set{String}()
    for eq in eqac.data
        cl = eq.num_classes
        for i in 0:3^cl-1
            vars_int = Int[]
            i0 = i
            for (j,x) in enumerate(eq.data)
                if j == x
                    push!(vars_int, i%3+1)
                    i ÷= 3
                else
                    push!(vars_int, vars_int[eq.data[x]])
                end
            end
            @assert i == 0
            last_var = 0
            for x in Iterators.reverse(vars_int)
                if last_var+1 == x
                    last_var = x
                elseif last_var < x
                    break
                end
            end
            if last_var != 3 continue end

            vars = [['A','B','C'][x] for x in vars_int]
            push!(instances, String(vars))
        end
    end
    count_b = length(instances)
    return count_a == count_b, count_a, count_b
end

catals = generate_catalan(6)
catal = catals[125]

shape = catalan_to_fml_shape(catal)
eqac = provable_eqac(shape)
println(test_count_above(eqac))
