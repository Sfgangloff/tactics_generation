import Batteries

open Std

def max_length_list (input_list : List (List Nat)) : Nat × List Nat :=
  match input_list with
  | [] => (0, [])
  | x :: xs =>
    let (bestLen, bestList) := xs.foldl (fun (acc : Nat × List Nat) (l : List Nat) =>
      let (bl, blist) := acc
      let len := l.length
      if len > bl then (len, l) else acc
    ) (x.length, x)
    (bestLen, bestList)

#guard max_length_list [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]] = (3, [13, 15, 17])
#guard max_length_list [[1,2,3,4,5],[1,2,3,4],[1,2,3],[1,2],[1]] = (5, [1,2,3,4,5])
#guard max_length_list [[3,4,5],[6,7,8,9],[10,11,12]] = (4, [6,7,8,9])
