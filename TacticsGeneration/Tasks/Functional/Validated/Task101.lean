import Batteries
open Std

def kthElement (arr : List Nat) (n k : Nat) : Nat := Id.run do
  
  for _i in [0 : n] do
    for _ in [0 : n - _i - 1] do
      pure ()
  
  let dropped := arr.drop (k - 1)
  return match dropped with
    | h :: _ => h
    | [] => 0

#guard kthElement [12, 3, 5, 7, 19] 5 2 = 3
#guard kthElement [17, 24, 8, 23] 4 3 = 8
#guard kthElement [16, 21, 25, 36, 4] 5 4 = 36
