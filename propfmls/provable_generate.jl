#=
provable_generate.jl

Main script for generating provable propositional logic theorems in Lean format.

Usage:
    julia provable_generate.jl <num_implications>

Example:
    julia provable_generate.jl 3

Output:
    Writes Lean theorem statements to TacticsGeneration/Output.lean
    Format: theorem propfmls_{n}_{shape_id}_{eq_id} (vars : Prop) : formula := by sorry

The generator:
1. Enumerates all formula shapes with n implications (Catalan structures)
2. Determines which are provable (via backward proof search)
3. Generates all distinct variable labelings that preserve provability
4. Outputs unique theorems ready for automated tactic generation
=#

include("equivalences.jl")
include("fml_shape.jl")
include("provable_count.jl")

"""
    eq_to_labels(eq :: Equivalence) -> Vector{Char}

Convert an equivalence relation to a variable labeling using letters A, B, C, ...

Assigns labels such that equivalent nodes get the same label, and labels
are assigned in reverse order (rightmost variables get labels first).

# Arguments
- `eq`: Equivalence relation on formula nodes

# Returns
Vector of characters where index i contains the label for node i.
Equivalent nodes receive the same label.

# Example
```julia
eq = Equivalence([1, 2, 1], 2)  # Nodes 1 and 3 equivalent, 2 separate
eq_to_labels(eq)  # ['A', 'B', 'A'] - nodes 1,3 both labeled A
```
"""
function eq_to_labels(eq :: Equivalence)
    res = fill('_', length(eq.data))
    next_label = 'A'
    # Assign labels in reverse order for aesthetic reasons
    # (rightmost/innermost variables get lower letters)
    for (i,x) in Iterators.reverse(enumerate(eq.data))
        if res[x] == '_'  # First time seeing this equivalence class
            res[x] = next_label
            next_label += 1
        end
        res[i] = res[x]  # Inherit label from representative
    end
    return res
end

# Parse command-line arguments
if length(ARGS) != 1
    println("Usage:")
    println("\$ julia provable_generate.jl <num_arrows>")
    println()
    println("Example:")
    println("\$ julia provable_generate.jl 3")
    println()
    println("Generates all provable propositional formulas with 3 implications")
    println("Output is written to TacticsGeneration/Output.lean")
    exit()
end

n = parse(Int, ARGS[1])

# Determine output file path relative to project root
script_dir = @__DIR__
project_root = dirname(script_dir)
output_file = joinpath(project_root, "TacticsGeneration", "Output.lean")

# Open output file for writing
open(output_file, "w") do io
    # Write Lean file header
    println(io, "/-!")
    println(io, "Auto-generated propositional logic theorems")
    println(io, "Generated with provable_generate.jl for n=$n implications")
    println(io, "-/")
    println(io)

    # Main generation loop
    catals = generate_catalan(n)  # Get all Catalan structures
    for (catal_i, catal) in enumerate(catals)
        shape = catalan_to_fml_shape(catal)  # Convert to formula shape
        eqac = provable_eqac(shape)  # Determine provable variable assignments

        # Generate one theorem for each provable variable assignment
        for (eq_i, eq) in enumerate(collect_above(eqac))
            labels = eq_to_labels(eq)  # Convert equivalence to variable names
            uq_labels = sort(collect(Set(labels)))  # Get unique labels (A, B, C, ...)

            # Output Lean theorem statement
            print(io, "theorem propfmls_$(n)_$(catal_i)_$(eq_i) (")
            for v in uq_labels
                print(io, v, ' ')
            end
            print(io, ": Prop) : ")
            show_with_labels(io, shape, labels, 1)
            println(io, " := by sorry")
        end
    end
end

println("Successfully generated theorems in: $output_file")
