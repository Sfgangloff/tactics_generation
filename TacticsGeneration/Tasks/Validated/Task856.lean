import Batteries
open Std

def find_Min_Swaps (arr : List Nat) (n : Nat) : Nat :=
  let xs := (arr.take n).reverse
  let rec go (xs : List Nat) (zeros acc : Nat) : Nat :=
    match xs with
    | [] => acc
    | x :: xs' =>
      if x = 0 then
        go xs' (zeros + 1) acc
      else if x = 1 then
        go xs' zeros (acc + zeros)
      else
        go xs' zeros acc
  go xs 0 0

#guard find_Min_Swaps [1,0,1,0] 4 = 3
#guard find_Min_Swaps [0,1,0] 3 = 1
#guard find_Min_Swaps [0,0,1,1,0] 5 = 2
