import Batteries

open Std

def checkSubset (test_tup1 test_tup2 : List Nat) : Bool :=
  let s1 : HashSet Nat := HashSet.ofList test_tup1
  test_tup2.all (fun x => s1.contains x)

#guard checkSubset [10, 4, 5, 6] [5, 10] == true
#guard checkSubset [1, 2, 3, 4] [5, 6] == false
#guard checkSubset [7, 8, 9, 10] [10, 8] == true
