import Batteries

open Std

def checkGreater (testTup1 testTup2 : List Nat) : Bool :=
  (List.zip testTup1 testTup2).all (fun p => p.fst < p.snd)

#guard checkGreater [10, 4, 5] [13, 5, 18] = true
#guard checkGreater [1, 2, 3] [2, 1, 4] = false
#guard checkGreater [4, 5, 6] [5, 6, 7] = true
