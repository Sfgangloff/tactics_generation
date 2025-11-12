import Base.(<=)

#bell_precomputed = [1]
bell_size = 15
bell_zero = zeros(Int, bell_size)
bell_precomputed = [zeros(Int, bell_size)]
bell_precomputed[1][1] = 1

function bell(n :: Int)
    while n > length(bell_precomputed)
        l = length(bell_precomputed)
        #bell_next = sum(binomial(l,k)*bell_precomputed[k] for k in 1:l)
        #bell_next += 1
        bell_next = [
            i*bell_precomputed[l][i]
            for i in 1:bell_size
        ]
        for i in 2:bell_size
            bell_next[i] += bell_precomputed[l][i-1]
        end
        push!(bell_precomputed, bell_next)
    end
    return bell_precomputed[n]
end

struct Equivalence
    data :: Vector{Int}
    num_classes :: Int
end
function Equivalence(data :: Vector{Int})
    num_classes =
        count(enumerate(data)) do (a,b)
            a == b
        end
    Equivalence(data, num_classes)
end

eq_empty(n :: Int) = Equivalence(collect(1:n), n)
eq_full(n :: Int) = Equivalence(ones(Int, n), 1)
function eq_pair(n, a,b)
    res = collect(1:n)
    num_classes = n-1

    if a > b res[a] = b
    elseif b > a res[b] = a
    else num_classes += 1
    end
    Equivalence(res, num_classes)
end
count_above(eq :: Equivalence) = bell(eq.num_classes)

function check(eq :: Equivalence)
    for (i,x) in enumerate(eq.data)
        @assert x <= i
        @assert x == eq.data[x]
    end
end

function join(eq1 :: Equivalence, eq2 :: Equivalence)
    res = copy(eq1.data)
    for (x,y) in enumerate(eq2.data)
        res[x] = res[res[x]]
        a = res[x]
        b = res[y]
        if a == b continue end
        if b < a a,b = b,a end
        for i in b:x if res[i] == b
            res[i] = a
        end end
    end
    return Equivalence(res)
end

leq(eq1 :: Equivalence, eq2 :: Equivalence) =
    all(enumerate(eq1.data)) do (i,x)
        eq2.data[i] == eq2.data[x]
    end
(<=)(eq1 :: Equivalence, eq2 :: Equivalence) = leq(eq1, eq2)

struct EqAC # Equivalence anti-chain
    data :: Vector{Equivalence}
end

function make_EqAC(data)
    data_sorted = sort(data, rev=true, by=(eq -> eq.num_classes))
    data_uq = []
    for next_eq in data_sorted
        if !any(eq -> eq <= next_eq, data_uq)
            push!(data_uq, next_eq)
        end
    end
    return EqAC(data_uq)
end

count_above(eq_ac :: EqAC) =
    if length(eq_ac.data) == 0
        return bell_zero
    elseif length(eq_ac.data) == 1
        return count_above(eq_ac.data[])
    else
        eq = eq_ac.data[1]
        eqs = eq_ac.data[2:end]
        return count_above(eq) + count_above(EqAC(eqs)) -
            count_above(make_EqAC([join(eq2,eq) for eq2 in eqs]))
    end

union(eq_ac1 :: EqAC, eq_ac2 :: EqAC) =
    if isempty(eq_ac1.data)
        eq_ac2
    elseif isempty(eq_ac2.data)
        eqac1
    else
        make_EqAC(vcat(eq_ac1.data, eq_ac2.data))
    end

intersect(eq_ac1 :: EqAC, eq_ac2 :: EqAC) =
    make_EqAC([join(eq1, eq2) for eq1 in eq_ac1.data for eq2 in eq_ac2.data])

all_equivalences_precomputed = Vector{Equivalence}[[eq_empty(1)]]

function all_equivalences(num_classes :: Int)
    while length(all_equivalences_precomputed) < num_classes
        prev = all_equivalences_precomputed[end]
        next = Equivalence[]
        for eq in prev
            data = copy(eq.data)
            push!(data, length(data)+1)
            push!(next, Equivalence(data, eq.num_classes+1))
            for (i,x) in enumerate(eq.data) if i == x
                data = copy(eq.data)
                push!(data, x)
                push!(next, Equivalence(data, eq.num_classes))
            end end
        end
        push!(all_equivalences_precomputed, next)
    end

    return all_equivalences_precomputed[num_classes]
end

function collect_above(eq :: Equivalence)
    big_to_small = zeros(Int, length(eq.data))
    small_to_big = Int[]
    for (i,x) in enumerate(eq.data) if i == x
        push!(small_to_big, x)
        big_to_small[x] = length(small_to_big)
    end end

    res = Equivalence[]
    for factor_eq in all_equivalences(eq.num_classes)
        data = [
            small_to_big[factor_eq.data[big_to_small[x]]]
            for x in eq.data
        ]
        push!(res, Equivalence(data, factor_eq.num_classes))
    end
    return res
end

function collect_above(eq_ac :: EqAC)
    res_a = Equivalence[]
    res_s = Set{Vector{Int}}()
    for bottom in eq_ac.data
        #println(bottom)
        for eq in collect_above(bottom)
            #println("  ", eq)
            if eq.data in res_s continue end
            push!(res_s, eq.data)
            push!(res_a, eq)
        end
    end
    return res_a
end
