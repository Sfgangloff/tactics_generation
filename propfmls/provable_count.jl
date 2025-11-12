function provable_eqac(shape :: FmlShape)
    #println("$shape")
    provable_eqac(shape, length(shape.data), 1, shape.data[1], Int[])
end

function provable_eqac(shape :: FmlShape, n :: Int, goal :: Int, hyps :: Vector{Int}, recent_goals :: Vector{Int})
    #println(">>")
    recent_goals = copy(recent_goals)
    push!(recent_goals, goal)
    res = EqAC(Equivalence[])
    #println("$recent_goals, $hyps, $goal")
    for h in hyps
        hyps2_all = Vector{Int}[]
        repetitive = false
        for subgoal in shape.data[h]
            hyps2 = copy(hyps)
            for a in shape.data[subgoal]
                if a ∉ hyps2
                    push!(hyps2, a)
                end
            end
            if length(hyps2) == length(hyps) && subgoal in recent_goals
                repetitive = true
                break
            end
            push!(hyps2_all, hyps2)
        end
        if repetitive continue end

        cur_sol = EqAC([eq_pair(n, goal, h)])
        for (subgoal, hyps2) in zip(shape.data[h], hyps2_all)
            rg2 =
                if length(hyps2) == length(hyps) recent_goals
                else Int[] end
            cur_sol = intersect(cur_sol, provable_eqac(shape, n, subgoal, hyps2, rg2))
        end
        res = union(res, cur_sol)
    end
    #println("<<")
    return res
end

