include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

function eq_to_labels(eq :: Equivalence)
    res = fill('_', length(eq.data))
    next_label = 'A'
    for (i,x) in Iterators.reverse(enumerate(eq.data))
        if res[x] == '_'
            res[x] = next_label
            next_label += 1
        end
        res[i] = res[x]
    end
    return res
end

if length(ARGS) != 1
    println("Usage:")
    println("\$ julia provable_generate.jl <num_arrows>")
    exit()
end

n = parse(Int, ARGS[1])
catals = generate_catalan(n)
for (catal_i, catal) in enumerate(catals)
    shape = catalan_to_fml_shape(catal)
    eqac = provable_eqac(shape)
    for (eq_i, eq) in enumerate(collect_above(eqac))
        labels = eq_to_labels(eq)
        uq_labels = sort(collect(Set(labels)))
        print("theorem propfmls_$(n)_$(catal_i)_$(eq_i) (")
        for v in uq_labels
            print(v, ' ')
        end
        print(": Prop) : ")
        show_with_labels(stdout, shape, labels, 1)
        println(" := by sorry")
    end
end
