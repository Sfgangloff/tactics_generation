import Batteries

open Std

def repeatTuples {α : Type} (test_tup : α) (N : Nat) : List α :=
  List.replicate N test_tup

#guard repeatTuples (1, 3) 4 = [(1, 3), (1, 3), (1, 3), (1, 3)]
#guard repeatTuples (1, 2) 3 = [(1, 2), (1, 2), (1, 2)]
#guard repeatTuples (3, 4) 5 = [(3, 4), (3, 4), (3, 4), (3, 4), (3, 4)]
