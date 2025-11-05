import Batteries

open Std

def testDuplicate (arraynums : List Int) : Bool :=
  let numsSet := arraynums.foldl (fun acc x => acc.insert x) HashSet.emptyWithCapacity
  arraynums.length ≠ numsSet.size

#guard testDuplicate [1, 2, 3, 4, 5] = false
#guard testDuplicate [1, 2, 3, 4, 4] = true
#guard testDuplicate [1, 1, 2, 2, 3, 3, 4, 4, 5] = true
