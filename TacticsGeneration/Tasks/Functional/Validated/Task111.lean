import Batteries
open Std

def commonInNestedLists (nestedlist : List (List Nat)) : List Nat :=
  match nestedlist with
  | [] => []
  | x::xs =>
    let sets := xs.map HashSet.ofList
    let common := sets.foldl (fun acc set => acc.filter (fun x => set.contains x)) (HashSet.ofList x)
    common.toList

def isort (xs : List Nat) : List Nat :=
  let rec insert (x : Nat) (ys : List Nat) : List Nat :=
    match ys with
    | [] => [x]
    | y :: ys' => if x ≤ y then x :: y :: ys' else y :: insert x ys'
  xs.foldl (fun sorted x => insert x sorted) []

#eval isort [18, 12]

#eval commonInNestedLists [[12, 18, 23, 25, 45], [7, 12, 18, 24, 28], [1, 5, 8, 12, 15, 16, 18]] == [12, 18]
#eval commonInNestedLists [[12, 5, 23, 25, 45], [7, 11, 5, 23, 28], [1, 5, 8, 18, 23, 16]] == [5, 23]
#eval commonInNestedLists [[2, 3, 4, 1], [4, 5], [6, 4, 8], [4, 5], [6, 8, 4]] == [4]

#eval commonInNestedLists [[12, 18, 23, 25, 45], [7, 12, 18, 24, 28], [1, 5, 8, 12, 15, 16, 18]] == [12, 18]
#eval commonInNestedLists [[12, 5, 23, 25, 45], [7, 11, 5, 23, 28], [1, 5, 8, 18, 23, 16]] == [5, 23]
#eval commonInNestedLists [[2, 3, 4, 1], [4, 5], [6, 4, 8], [4, 5], [6, 8, 4]] == [4]
