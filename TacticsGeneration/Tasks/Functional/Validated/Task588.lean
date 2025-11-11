import Batteries

open Std

def bigDiff (nums : List Nat) : Nat :=
  match nums with
  | [] => 0
  | x :: xs =>
    let (mn, mx) := xs.foldl (fun (acc : Nat × Nat) y =>
      let a := acc.fst
      let b := acc.snd
      let a' := if y < a then y else a
      let b' := if y > b then y else b
      (a', b')
    ) (x, x)
    mx - mn

#guard bigDiff [1,2,3,4] == 3
#guard bigDiff [4,5,12] == 8
#guard bigDiff [9,2,3] == 7
