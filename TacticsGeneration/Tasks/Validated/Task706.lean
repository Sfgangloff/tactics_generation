import Batteries

open Std

def isSubset (arr1 : List Nat) (m : Nat) (arr2 : List Nat) (n : Nat) : Bool := Id.run do
  let s : HashSet Nat := HashSet.ofList (arr1.take m)
  for x in arr2.take n do
    if x ∈ s then
      pure ()
    else
      return false
  return true

#guard isSubset [11, 1, 13, 21, 3, 7] 6 [11, 3, 7, 1] 4 == true
#guard isSubset [1, 2, 3, 4, 5, 6] 6 [1, 2, 4] 3 == true
#guard isSubset [10, 5, 2, 23, 19] 5 [19, 5, 3] 3 == false
