import Batteries

open Std

def testDistinct (data : List Nat) : Bool :=
  let dataHashSet := HashSet.ofList data
  data.length == dataHashSet.size

#guard testDistinct [1, 5, 7, 9] = true
#guard testDistinct [2, 4, 5, 5, 7, 9] = false
#guard testDistinct [1, 2, 3] = true
