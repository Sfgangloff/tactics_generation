import Batteries

open Std

def nthItems (list : List Nat) (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let rec go (xs : List Nat) (i : Nat) : List Nat :=
      match xs with
      | [] => []
      | x :: xs' =>
        if i % n == 0 then
          x :: go xs' (i + 1)
        else
          go xs' (i + 1)
    go list 0

#guard nthItems [1, 2, 3, 4, 5, 6, 7, 8, 9] 2 == [1, 3, 5, 7, 9]
#guard nthItems [10, 15, 19, 17, 16, 18] 3 == [10, 17]
#guard nthItems [14, 16, 19, 15, 17] 4 == [14, 17]
