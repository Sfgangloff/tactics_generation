import Batteries

open Std

def multiplyElements (test_tup : List Nat) : List Nat :=
  (List.zip test_tup (test_tup.drop 1)).map (fun (p : Nat × Nat) => p.fst * p.snd)

#guard multiplyElements [1, 5, 7, 8, 10] = [5, 35, 56, 80]
#guard multiplyElements [2, 4, 5, 6, 7] = [8, 20, 30, 42]
#guard multiplyElements [12, 13, 14, 9, 15] = [156, 182, 126, 135]
