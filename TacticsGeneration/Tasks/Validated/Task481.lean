import Batteries

open Std

def isSubsetSum (set : List Nat) (n : Nat) (sum : Nat) : Bool :=
  match n with
  | 0 => sum == 0
  | n+1 =>
    if sum == 0 then true
    else
      let v := set.getD n 0
      if v > sum then
        isSubsetSum set n sum
      else
        isSubsetSum set n sum || isSubsetSum set n (sum - v)

#guard isSubsetSum [3, 34, 4, 12, 5, 2] 6 9 == true
#guard isSubsetSum [3, 34, 4, 12, 5, 2] 6 30 == false
#guard isSubsetSum [3, 34, 4, 12, 5, 2] 6 15 == true
