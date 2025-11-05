import Batteries

open Std

def unique_Element (arr : List Nat) (n : Nat) : String :=
  let s : HashSet Nat := HashSet.ofList arr
  if s.size == 1 then "YES" else "NO"

#guard unique_Element [1,1,1] 3 = "YES"
#guard unique_Element [1,2,1,2] 4 = "NO"
#guard unique_Element [1,2,3,4,5] 5 = "NO"
