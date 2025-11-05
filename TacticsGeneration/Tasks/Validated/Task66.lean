import Batteries

open Std

def posCount (list : List Int) : Nat :=
  list.foldl (fun acc num => if num >= 0 then acc + 1 else acc) 0

#guard posCount [1, -2, 3, -4] == 2
#guard posCount [3, 4, 5, -1] == 3
#guard posCount [1, 2, 3, 4] == 4
