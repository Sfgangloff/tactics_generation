#=
fml_shape.jl

Defines the syntactic structure of propositional implication formulas.
Formulas are represented as trees where each node has a list of assumption
children and represents an implication: (assump₁ → (assump₂ → ... → goal)).

The number of possible formula shapes with n implications equals the n-th
Catalan number, as these correspond to different ways of parenthesizing
nested implications.
=#

import Base.show

"""
    FmlShape

Represents the shape (syntactic structure) of a propositional formula
built from implications.

# Fields
- `data :: Vector{Vector{Int}}`: For each node i, data[i] contains indices
  of its assumption children (the premises in the implication chain)

# Structure
Node 1 is the root (main goal). Each node represents a subformula.
For node i with assumptions [a₁, a₂, ..., aₖ]:
  Formula at i = (aₖ → (aₖ₋₁ → ... → (a₁ → i)))

# Example
```julia
# Shape for (A → B) → B:
# Node 1 (goal B): assumptions [2]
# Node 2 (A → B): assumptions [3]
# Node 3 (A): assumptions []
data = [[], [3], [2]]
shape = FmlShape(data)
```
"""
struct FmlShape
    data :: Vector{Vector{Int}}
end

"""
    FmlSubShape

Helper struct for pretty-printing subformulas within a FmlShape.

# Fields
- `shape :: FmlShape`: The complete formula shape
- `root :: Int`: Index of the subformula root node
"""
struct FmlSubShape
    shape :: FmlShape
    root :: Int
end

"""
    Base.show(io::IO, sub_shape :: FmlSubShape)

Pretty-print a subformula in implication notation with parentheses.
Displays as: (assumpₙ -> ... -> assump₁ -> goal)
"""
function Base.show(io::IO, sub_shape :: FmlSubShape)
    root = sub_shape.root
    shape = sub_shape.shape
    assumps = shape.data[root]
    if isempty(assumps)
        show(io, root)  # Atomic variable
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

"""
    Base.show(io::IO, shape :: FmlShape)

Pretty-print a formula shape starting from the root (node 1).
"""
function Base.show(io::IO, shape :: FmlShape)
    show(io, FmlSubShape(shape, 1))
end

"""
    show_with_labels(io::IO, shape :: FmlShape, labels, root :: Int)

Pretty-print a formula with variable labels (e.g., A, B, C) instead of node numbers.

# Arguments
- `io`: Output stream
- `shape`: Formula shape to display
- `labels`: Vector or array mapping node indices to labels (typically characters)
- `root`: Starting node index

# Output Format
Uses Unicode arrow (→) and displays as: (labelₙ → ... → label₁ → label_goal)
"""
function show_with_labels(io::IO, shape :: FmlShape, labels, root :: Int)
    assumps = shape.data[root]
    if !isempty(assumps); print(io, '(') end
    for assump in Iterators.reverse(assumps)
        show_with_labels(io, shape, labels, assump)
        print(io, " → ")
    end
    print(io, labels[root])
    if !isempty(assumps); print(io, ')') end
end

"""
    println_with_labels(shape :: FmlShape, labels)

Print a formula with labels to stdout, followed by a newline.
"""
function println_with_labels(shape :: FmlShape, labels)
    show_with_labels(stdout, shape, labels, 1)
    println()
end

"""
    tostr_with_labels(shape :: FmlShape, labels) -> String

Convert a formula with labels to a string representation.
"""
function tostr_with_labels(shape :: FmlShape, labels)
    io = IOBuffer()
    show_with_labels(io, shape, labels, 1)
    return String(take!(io))
end


"""
    generate_catalan(n) -> Vector{Vector{Int}}

Generate all Catalan structures of size n using Dyck paths.

A Dyck path is a sequence of +1 (up) and -1 (down) steps that:
- Starts at 0
- Never goes below 0
- Ends at 0 after 2n steps

The number of such paths is the n-th Catalan number: C(n) = (2n)! / ((n+1)! * n!)
For n = 0,1,2,3,4: C(n) = 1,1,2,5,14

# Arguments
- `n`: Size parameter (number of implications in resulting formulas)

# Returns
Vector of Dyck paths, each represented as a vector of +1 and -1 values.
Each path encodes a unique way to parenthesize n implications.

# Example
```julia
generate_catalan(2)  # Returns 2 Catalan structures:
# [1, 1, -1, -1]  corresponds to ((A → B) → C)
# [1, -1, 1, -1]  corresponds to (A → (B → C))
```
"""
function generate_catalan(n)
    working_arr = zeros(2*n)
    res = Vector{Int}[]
    # Recursive backtracking to generate all valid Dyck paths
    function recurse(a,b)
        # a = number of -1's placed, b = number of +1's placed
        if a == n
            push!(res, copy(working_arr))
        else
            # Can always add +1 if we haven't reached n
            if b < n
                working_arr[a+b+1] = 1
                recurse(a,b+1)
            end
            # Can only add -1 if current height > 0 (more +1's than -1's)
            if a < b
                working_arr[a+b+1] = -1
                recurse(a+1,b)
            end
        end
    end
    recurse(0,0)
    return res
end

"""
    catalan_to_fml_shape(catal :: Vector{Int}) -> FmlShape

Convert a Catalan structure (Dyck path) to a formula shape.

# Algorithm
Interpret the Dyck path as a sequence of "open implication" (+1) and
"close implication" (-1) operations, building the formula tree structure.

# Arguments
- `catal`: Dyck path (vector of +1 and -1 values from generate_catalan)

# Returns
FmlShape representing the implication structure encoded by the Dyck path.

# Example
```julia
# [1, -1, 1, -1] represents: open, close, open, close
# This builds: A → (B → C)
# Node 1 (goal): assumptions [2]
# Node 2: assumptions [3]
# Node 3: assumptions []
```
"""
function catalan_to_fml_shape(catal :: Vector{Int})
    res = Vector{Int}[]
    index = 1
    catal = vcat([1], catal, [-1])  # Wrap entire formula
    # Recursive descent parser for Dyck path
    function recurse()
        index += 1
        local_res = Int[]
        push!(res, local_res)
        # Process all assumptions (nested implications) before this node
        while catal[index] == 1
            push!(local_res, length(res)+1)  # Add assumption reference
            recurse()  # Parse assumption subformula
        end
        index += 1  # Skip closing -1
    end
    recurse()
    return FmlShape(res)
end
