import Batteries

open Std

inductive PyVal where
  | num : Nat → PyVal
  | tup : List PyVal → PyVal

def countElim (num : List PyVal) : Nat :=
  let rec loop (l : List PyVal) (acc : Nat) : Nat :=
    match l with
    | [] => acc
    | PyVal.tup _ :: _ => acc
    | PyVal.num _ :: xs => loop xs (acc + 1)
  loop num 0

#guard countElim [PyVal.num 10, PyVal.num 20, PyVal.num 30, PyVal.tup [PyVal.num 10, PyVal.num 20], PyVal.num 40] = 3
#guard countElim [PyVal.num 10, PyVal.tup [PyVal.num 20, PyVal.num 30], PyVal.tup [PyVal.num 10, PyVal.num 20], PyVal.num 40] = 1
#guard countElim [PyVal.tup [PyVal.num 10, PyVal.tup [PyVal.num 20, PyVal.num 30, PyVal.tup [PyVal.num 10, PyVal.num 20], PyVal.num 40]]] = 0
