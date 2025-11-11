import Batteries

open Std

def count_samepair (list1 list2 list3 : List Nat) : Nat :=
  match list1, list2, list3 with
  | m :: ms, n :: ns, o :: os =>
    let inc := if (m == n) && (n == o) then 1 else 0
    inc + count_samepair ms ns os
  | _, _, _ => 0

#guard count_samepair [1,2,3,4,5,6,7,8] [2,2,3,1,2,6,7,9] [2,1,3,1,2,6,7,9] = 3
#guard count_samepair [1,2,3,4,5,6,7,8] [2,2,3,1,2,6,7,8] [2,1,3,1,2,6,7,8] = 4
#guard count_samepair [1,2,3,4,2,6,7,8] [2,2,3,1,2,6,7,8] [2,1,3,1,2,6,7,8] = 5
