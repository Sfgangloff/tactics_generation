import Batteries

open Std

def count (lst : List Bool) : Nat := lst.foldl (fun acc b => if b then acc + 1 else acc) 0

#guard count [true, false, true] == 2
#guard count [false, false] == 0
#guard count [true, true, true] == 3
