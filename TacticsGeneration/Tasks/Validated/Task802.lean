import Batteries
open Std

def countRotation (arr : List Nat) (n : Nat) : Nat :=
  let arr' := arr.take n
  let rec loop (lst : List Nat) (i : Nat) : Nat :=
    match lst with
    | x :: y :: xs =>
      if y < x then
        i
      else
        loop (y :: xs) (i + 1)
    | _ => 0
  loop arr' 1

#guard countRotation [3, 2, 1] 3 = 1
#guard countRotation [4, 5, 1, 2, 3] 5 = 2
#guard countRotation [7, 8, 9, 1, 2, 3] 6 = 3
