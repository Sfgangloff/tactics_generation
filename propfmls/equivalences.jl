#=
equivalences.jl

Implements equivalence relations and Bell number computations for tracking
which atomic propositions in propositional formulas can be unified.

Key concepts:
- Equivalence: Represents a partition of n elements (formula variables)
- EqAC (Equivalence Anti-Chain): Collection of maximal equivalence relations
- Bell numbers: Count the number of ways to partition a set

These structures are used to eliminate duplicate formulas that differ only
in variable renaming (e.g., A→B is equivalent to C→D).
=#

import Base.(<=)

# Bell number computation using triangle method (similar to Pascal's triangle)
# Bell numbers count the number of partitions of a set of n elements
# Sequence: 1, 1, 2, 5, 15, 52, 203, 877, 4140, ...
bell_size = 15
bell_zero = zeros(Int, bell_size)
bell_precomputed = [zeros(Int, bell_size)]
bell_precomputed[1][1] = 1

"""
    bell(n :: Int) -> Vector{Int}

Compute the n-th row of the Bell triangle using dynamic programming.
Returns a vector where index i contains B(n,i) - the number of partitions
of n elements into exactly i non-empty subsets.

The sum of the returned vector equals the n-th Bell number B(n).

# Example
```julia
bell(3)  # Returns vector representing partitions of 3 elements
# [1, 3, 1, 0, ...] means: 1 partition into 1 subset, 3 into 2 subsets, 1 into 3 subsets
```
"""
function bell(n :: Int)
    # Compute Bell triangle rows on demand and cache them
    while n > length(bell_precomputed)
        l = length(bell_precomputed)
        # Build next row: each entry = i * prev[i] (from same column)
        bell_next = [
            i*bell_precomputed[l][i]
            for i in 1:bell_size
        ]
        # Add prev[i-1] (from left diagonal)
        for i in 2:bell_size
            bell_next[i] += bell_precomputed[l][i-1]
        end
        push!(bell_precomputed, bell_next)
    end
    return bell_precomputed[n]
end

"""
    Equivalence

Represents an equivalence relation (partition) on n elements using the
union-find data structure representation.

# Fields
- `data :: Vector{Int}`: data[i] points to the representative of i's equivalence class
  Invariant: data[i] <= i, and data[i] == i iff i is a class representative
- `num_classes :: Int`: Number of equivalence classes in the partition

# Interpretation
Elements i and j are equivalent iff they have the same representative
(reached by following data pointers to fixed points).

# Example
```julia
# Partition {1,3}, {2}, {4,5} on 5 elements:
eq = Equivalence([1, 2, 1, 4, 4], 3)  # 3 classes
# data[1]=1, data[3]=1 → 1 and 3 are equivalent
# data[4]=4, data[5]=4 → 4 and 5 are equivalent
# data[2]=2 → 2 is in its own class
```
"""
struct Equivalence
    data :: Vector{Int}
    num_classes :: Int
end

"""
    Equivalence(data :: Vector{Int})

Construct an Equivalence from a data vector, automatically computing
the number of equivalence classes.
"""
function Equivalence(data :: Vector{Int})
    num_classes =
        count(enumerate(data)) do (a,b)
            a == b  # Count how many elements are their own representative
        end
    Equivalence(data, num_classes)
end

"""
    eq_empty(n :: Int) -> Equivalence

Create the discrete equivalence relation on n elements where each element
is in its own equivalence class: {1}, {2}, ..., {n}.
"""
eq_empty(n :: Int) = Equivalence(collect(1:n), n)

"""
    eq_full(n :: Int) -> Equivalence

Create the complete equivalence relation on n elements where all elements
are in a single equivalence class: {1,2,...,n}.
"""
eq_full(n :: Int) = Equivalence(ones(Int, n), 1)

"""
    eq_pair(n, a, b) -> Equivalence

Create an equivalence relation on n elements where only a and b are
equivalent (if a ≠ b), all others in separate classes.

# Arguments
- `n`: Total number of elements
- `a`, `b`: Elements to unify (1-indexed)

# Returns
Equivalence with n-1 classes if a ≠ b, n classes if a == b.
"""
function eq_pair(n, a,b)
    res = collect(1:n)
    num_classes = n-1

    if a > b res[a] = b
    elseif b > a res[b] = a
    else num_classes += 1  # a == b, no unification needed
    end
    Equivalence(res, num_classes)
end

"""
    count_above(eq :: Equivalence) -> Vector{Int}

Count how many ways the equivalence relation can be refined.
Returns a Bell triangle row for the number of classes.

This counts formulas that are "above" this equivalence (where "above" means
variables can be further unified beyond what eq specifies).
"""
count_above(eq :: Equivalence) = bell(eq.num_classes)

"""
    check(eq :: Equivalence)

Verify that an Equivalence satisfies its data structure invariants:
1. Each element points to an element <= itself (data[i] <= i)
2. Each element's representative is idempotent (data[data[i]] == data[i])

Throws an assertion error if invariants are violated.
"""
function check(eq :: Equivalence)
    for (i,x) in enumerate(eq.data)
        @assert x <= i  # Representatives must be smaller indices
        @assert x == eq.data[x]  # Representatives are fixed points
    end
end

"""
    join(eq1 :: Equivalence, eq2 :: Equivalence) -> Equivalence

Compute the join (least upper bound) of two equivalence relations.
The result is the coarsest equivalence relation that refines both inputs.

In set terms: i ≡ j in result iff i ≡ j in eq1 OR i ≡ j in eq2 (transitively).

# Algorithm
Path compression union-find: merges equivalence classes incrementally
while maintaining the invariant that data[i] <= i.

# Example
```julia
# eq1: {1,2}, {3}
# eq2: {1}, {2,3}
# join: {1,2,3} - transitively merges all three
```
"""
function join(eq1 :: Equivalence, eq2 :: Equivalence)
    res = copy(eq1.data)
    # Process each equivalence in eq2
    for (x,y) in enumerate(eq2.data)
        # Path compression: ensure we're using current representatives
        res[x] = res[res[x]]
        a = res[x]
        b = res[y]
        if a == b continue end  # Already in same class
        if b < a a,b = b,a end  # Ensure a < b (smaller index is representative)
        # Merge: redirect all elements pointing to b to point to a
        for i in b:x if res[i] == b
            res[i] = a
        end end
    end
    return Equivalence(res)
end

"""
    leq(eq1 :: Equivalence, eq2 :: Equivalence) -> Bool
    (<=)(eq1 :: Equivalence, eq2 :: Equivalence) -> Bool

Check if eq1 is a refinement of eq2 (eq1 ≤ eq2 in the lattice of partitions).

Returns true iff: whenever i ≡ j in eq1, then i ≡ j in eq2.
Equivalently: eq2's partition is coarser than or equal to eq1's.

# Example
```julia
eq1 = Equivalence([1,2,1,4,4], 3)  # {1,3}, {2}, {4,5}
eq2 = Equivalence([1,1,1,4,4], 2)  # {1,2,3}, {4,5}
eq1 <= eq2  # true: eq1 is finer, eq2 is coarser
```
"""
leq(eq1 :: Equivalence, eq2 :: Equivalence) =
    all(enumerate(eq1.data)) do (i,x)
        eq2.data[i] == eq2.data[x]  # If i≡x in eq1, must have i≡x in eq2
    end
(<=)(eq1 :: Equivalence, eq2 :: Equivalence) = leq(eq1, eq2)

"""
    EqAC (Equivalence Anti-Chain)

Represents a set of equivalence relations where no element refines another.
This is an "anti-chain" in the lattice of partitions.

# Fields
- `data :: Vector{Equivalence}`: Collection of maximal (incomparable) equivalences

# Purpose
Used to compactly represent sets of formulas. Instead of storing all provable
variable assignments explicitly, we store only the "minimal" ones - those that
don't imply any others in the set.

# Invariant
For any two distinct equivalences eq1, eq2 in data:
- NOT (eq1 <= eq2) and NOT (eq2 <= eq1)  [incomparable]

# Example
```julia
# Instead of storing both {1,2,3} and {1,2},{3} (redundant since first implies second),
# we only store {1,2},{3} (the finer/more refined one)
```
"""
struct EqAC # Equivalence anti-chain
    data :: Vector{Equivalence}
end

"""
    make_EqAC(data) -> EqAC

Construct an anti-chain from a collection of equivalences by removing
redundancies. Keeps only maximal elements (those not refined by any other).

# Algorithm
1. Sort by number of classes (descending) for efficiency
2. For each equivalence, keep it only if no previously kept equivalence refines it

# Returns
EqAC with no redundant equivalences (all pairwise incomparable).
"""
function make_EqAC(data)
    data_sorted = sort(data, rev=true, by=(eq -> eq.num_classes))
    data_uq = []
    for next_eq in data_sorted
        # Keep next_eq only if no existing eq refines it (eq <= next_eq)
        if !any(eq -> eq <= next_eq, data_uq)
            push!(data_uq, next_eq)
        end
    end
    return EqAC(data_uq)
end

"""
    count_above(eq_ac :: EqAC) -> Vector{Int}

Count all equivalences (variable assignments) that refine at least one equivalence
in the anti-chain. Uses inclusion-exclusion principle to avoid double-counting.

An equivalence E "refines" an anti-chain member M if E <= M, meaning E is more
specific (has more equivalence classes / fewer variables unified).

# Algorithm (Inclusion-Exclusion)
For anti-chain {E₁, E₂, ...}, count equivalences where (E <= E₁) OR (E <= E₂) OR ...:
- count({E : E <= E₁ or E <= E₂}) = count({E : E <= E₁}) + count({E : E <= E₂})
                                     - count({E : E <= E₁ and E <= E₂})
- Note: E <= E₁ and E <= E₂ iff E <= join(E₁, E₂)
- Recursively applies to larger sets

# Returns
Bell triangle row representing the count distribution by number of equivalence classes.

# Example
```julia
# Anti-chain with one member: {A,B}, {C}  (2 classes)
# Refinements: {A,B},{C} and {A},{B},{C}  (2 + 1 = 3 total from Bell(2))
# count_above returns [0, 1, 1, 0, ...] meaning 1 with 2 classes, 1 with 3 classes
```
"""
count_above(eq_ac :: EqAC) =
    if length(eq_ac.data) == 0
        return bell_zero  # Empty set: no formulas
    elseif length(eq_ac.data) == 1
        return count_above(eq_ac.data[])  # Single equivalence
    else
        # Inclusion-exclusion: count(E₁ ∪ rest) = count(E₁) + count(rest) - count(E₁ ∩ rest)
        eq = eq_ac.data[1]
        eqs = eq_ac.data[2:end]
        return count_above(eq) + count_above(EqAC(eqs)) -
            count_above(make_EqAC([join(eq2,eq) for eq2 in eqs]))
    end

"""
    union(eq_ac1 :: EqAC, eq_ac2 :: EqAC) -> EqAC

Compute the union of two anti-chains.
Result represents formulas satisfying at least one equivalence from either input.
"""
union(eq_ac1 :: EqAC, eq_ac2 :: EqAC) =
    if isempty(eq_ac1.data)
        eq_ac2
    elseif isempty(eq_ac2.data)
        eq_ac1
    else
        make_EqAC(vcat(eq_ac1.data, eq_ac2.data))
    end

"""
    intersect(eq_ac1 :: EqAC, eq_ac2 :: EqAC) -> EqAC

Compute the intersection of two anti-chains.
Result represents formulas satisfying at least one equivalence from BOTH inputs.

# Algorithm
Take all pairwise joins: {join(e1, e2) | e1 ∈ ac1, e2 ∈ ac2}
The join represents the union of constraints from both equivalences.
"""
intersect(eq_ac1 :: EqAC, eq_ac2 :: EqAC) =
    make_EqAC([join(eq1, eq2) for eq1 in eq_ac1.data for eq2 in eq_ac2.data])

# Cache for generating all equivalences on n elements
all_equivalences_precomputed = Vector{Equivalence}[[eq_empty(1)]]

"""
    all_equivalences(num_classes :: Int) -> Vector{Equivalence}

Generate all possible equivalence relations on num_classes elements.
Returns the list of all partitions of {1, 2, ..., num_classes}.

# Algorithm (Dynamic Programming)
Build equivalences on n+1 elements from equivalences on n elements:
1. Add new element as singleton class (increases class count by 1)
2. Add new element to each existing class (preserves class count)

# Caching
Results are cached in `all_equivalences_precomputed` for efficiency.

# Returns
Vector of all equivalence relations with exactly num_classes elements.
The number of returned equivalences equals the Bell number B(num_classes).

# Example
```julia
all_equivalences(3)  # Returns 5 partitions:
# {1},{2},{3}
# {1,2},{3}
# {1,3},{2}
# {1},{2,3}
# {1,2,3}
```
"""
function all_equivalences(num_classes :: Int)
    # Build incrementally using dynamic programming
    while length(all_equivalences_precomputed) < num_classes
        prev = all_equivalences_precomputed[end]
        next = Equivalence[]
        for eq in prev
            # Option 1: Add new element as singleton (new class)
            data = copy(eq.data)
            push!(data, length(data)+1)
            push!(next, Equivalence(data, eq.num_classes+1))
            # Option 2: Add new element to each existing class
            for (i,x) in enumerate(eq.data) if i == x  # i is a class representative
                data = copy(eq.data)
                push!(data, x)  # New element joins class of representative x
                push!(next, Equivalence(data, eq.num_classes))
            end end
        end
        push!(all_equivalences_precomputed, next)
    end

    return all_equivalences_precomputed[num_classes]
end

"""
    collect_above(eq :: Equivalence) -> Vector{Equivalence}

Generate all equivalences that refine (are more specific than) the given equivalence.
These represent all possible ways to further partition eq's equivalence classes.

# Algorithm
1. Map eq's classes to a factored space {1, ..., k} where k = num_classes
2. Generate all partitions of this k-element space
3. Map back to original n-element space using the factorization

# Returns
All equivalences E where E <= eq (E refines eq).
Count equals Bell number B(eq.num_classes).

# Example
```julia
eq = Equivalence([1,2,1], 2)  # {1,3}, {2} - two classes
collect_above(eq)  # Returns Bell(2) = 2 refinements:
# 1. {1,3}, {2}     (keep as is)
# 2. {1}, {2}, {3}  (split first class)
```
"""
function collect_above(eq :: Equivalence)
    # Build mappings between original space and factored space
    big_to_small = zeros(Int, length(eq.data))
    small_to_big = Int[]
    for (i,x) in enumerate(eq.data) if i == x  # Class representatives
        push!(small_to_big, x)
        big_to_small[x] = length(small_to_big)
    end end

    # Generate all refinements by partitioning the factored space
    res = Equivalence[]
    for factor_eq in all_equivalences(eq.num_classes)
        # Map factored partition back to original space
        data = [
            small_to_big[factor_eq.data[big_to_small[x]]]
            for x in eq.data
        ]
        push!(res, Equivalence(data, factor_eq.num_classes))
    end
    return res
end

"""
    collect_above(eq_ac :: EqAC) -> Vector{Equivalence}

Generate all equivalences that satisfy at least one equivalence in the anti-chain.
Returns the union of all refinements of each equivalence in eq_ac.

# Algorithm
1. For each bottom equivalence in eq_ac, generate all its refinements
2. Deduplicate using a set to avoid redundant equivalences
3. Return unique list

# Returns
Vector of all equivalences that refine at least one element of eq_ac.
"""
function collect_above(eq_ac :: EqAC)
    res_a = Equivalence[]
    res_s = Set{Vector{Int}}()
    for bottom in eq_ac.data
        for eq in collect_above(bottom)
            if eq.data in res_s continue end  # Skip duplicates
            push!(res_s, eq.data)
            push!(res_a, eq)
        end
    end
    return res_a
end
