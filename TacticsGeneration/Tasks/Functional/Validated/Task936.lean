import Batteries
open Std

def reArrangeTuples (testList : List (Nat × Nat)) (ordList : List Nat) : List (Nat × Nat) :=
  let rec find (l : List (Nat × Nat)) (k : Nat) : Nat :=
    match l with
    | [] => 0
    | (a, b) :: t => if a = k then b else find t k
  ordList.map (fun key => (key, find testList key))

#guard reArrangeTuples [(4, 3), (1, 9), (2, 10), (3, 2)] [1, 4, 2, 3] = [(1, 9), (4, 3), (2, 10), (3, 2)]
#guard reArrangeTuples [(5, 4), (2, 10), (3, 11), (4, 3)] [3, 4, 2, 3] = [(3, 11), (4, 3), (2, 10), (3, 11)]
#guard reArrangeTuples [(6, 3), (3, 8), (5, 7), (2, 4)] [2, 5, 3, 6] = [(2, 4), (5, 7), (3, 8), (6, 3)]
