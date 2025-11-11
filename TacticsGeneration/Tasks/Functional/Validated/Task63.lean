import Batteries
open Std

def absDiff (a b : Nat) : Nat :=
  if b ≥ a then b - a else a - b

def maxDifference (testList : List (Nat × Nat)) : Nat :=
  let temp := testList.map (fun (a, b) => absDiff b a)
  temp.foldl Nat.max 0

#eval maxDifference [(3, 5), (1, 7), (10, 3), (1, 2)] == 7
#eval maxDifference [(4, 6), (2, 17), (9, 13), (11, 12)] == 15
#eval maxDifference [(12, 35), (21, 27), (13, 23), (41, 22)] == 23
