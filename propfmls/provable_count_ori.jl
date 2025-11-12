function provable_eqac(shape :: FmlShape)
    provable_eqac(shape, length(shape.data), 1, Int[])
end

function provable_eqac(shape :: FmlShape, n :: Int, root :: Int, hyps :: Vector{Int})
    hyps = vcat(hyps, shape.data[root])
    res = EqAC(Equivalence[])
    for h in hyps
        hyps2 = filter((h2 -> h2 != h), hyps)
        cur_sol = EqAC([eq_pair(n, root, h)])
        for subgoal in shape.data[h]
            cur_sol = intersect(cur_sol, provable_eqac(shape, n, subgoal, hyps2))
        end
        res = union(res, cur_sol)
    end
    return res
end
