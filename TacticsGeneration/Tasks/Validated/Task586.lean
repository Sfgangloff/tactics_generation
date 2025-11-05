import Batteries

open Std

def split_Arr (a : List Nat) (n k : Nat) : List Nat :=
  let b := a.take k
  (a.drop k) ++ b

#guard split_Arr [12,10,5,6,52,36] 6 2 = [5,6,52,36,12,10]
#guard split_Arr [1,2,3,4] 4 1 = [2,3,4,1]
#guard split_Arr [0,1,2,3,4,5,6,7] 8 3 = [3,4,5,6,7,0,1,2]
