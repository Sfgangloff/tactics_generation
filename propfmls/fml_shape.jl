
import Base.show

struct FmlShape
    data :: Vector{Vector{Int}}
end
struct FmlSubShape
    shape :: FmlShape
    root :: Int
end

function Base.show(io::IO, sub_shape :: FmlSubShape)
    root = sub_shape.root
    shape = sub_shape.shape
    assumps = shape.data[root]
    if isempty(assumps)
        show(io, root)
    else
        print(io, '(')
        for assump in Iterators.reverse(assumps)
            show(io, FmlSubShape(shape, assump))
            print(io, " -> ")            
        end
        show(io, root)
        print(io, ')')
    end
end
function Base.show(io::IO, shape :: FmlShape)
    show(io, FmlSubShape(shape, 1))
end

function show_with_labels(io::IO, shape :: FmlShape, labels, root :: Int)
    assumps = shape.data[root]
    if !isempty(assumps); print(io, '(') end
    for assump in Iterators.reverse(assumps)
        show_with_labels(io, shape, labels, assump)
        print(io, " → ")
    end
    print(io, labels[root])
    # for assump in Iterators.reverse(assumps)
    if !isempty(assumps); print(io, ')') end
    # print(io, ')')
    # end
end
function println_with_labels(shape :: FmlShape, labels)
    show_with_labels(stdout, shape, labels, 1)
    println()
end
function tostr_with_labels(shape :: FmlShape, labels)
    io = IOBuffer()
    show_with_labels(io, shape, labels, 1)
    return String(take!(io))
end


function generate_catalan(n)
    working_arr = zeros(2*n)
    res = Vector{Int}[]
    function recurse(a,b)
        if a == n
            push!(res, copy(working_arr))
        else
            if b < n
                working_arr[a+b+1] = 1
                recurse(a,b+1)
            end
            if a < b
                working_arr[a+b+1] = -1
                recurse(a+1,b)
            end
        end
    end
    recurse(0,0)
    return res
end

function catalan_to_fml_shape(catal :: Vector{Int})
    res = Vector{Int}[]
    index = 1
    catal = vcat([1], catal, [-1])
    function recurse()
        index += 1
        local_res = Int[]
        push!(res, local_res)
        while catal[index] == 1
            push!(local_res, length(res)+1)
            recurse()
        end
        index += 1
    end
    recurse()
    return FmlShape(res)
end
