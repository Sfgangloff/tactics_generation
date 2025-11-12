include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

catals = generate_catalan(6)
for (catal_i, catal) in enumerate(catals)
    shape = catalan_to_fml_shape(catal)
    eqac = provable_eqac(shape)
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
            #println_with_labels(shape, vars)
            push!(instances, tostr_with_labels(shape, vars))
        end
    end
    count_b = length(instances)
    if count_a != count_b
        println("$catal_i: $shape")
        println(count_a)
        println(count_b)
    end

    #display(eqac.data)
    #println()
    #println()
end
