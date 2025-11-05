import Batteries

open Std

def extractUnique (testDict : List (String × List Nat)) : List Nat := Id.run do
  
  let mut s : HashSet Nat := {}
  let mut maxV : Nat := 0
  for (_, vals) in testDict do
    for v in vals do
      s := s.insert v
      if v > maxV then maxV := v
  
  let mut res : Array Nat := #[]
  for k in [0 : maxV + 1] do
    if s.contains k then
      res := res.push k
  return res.toList

#guard extractUnique [("msm", [5, 6, 7, 8]), ("is", [10, 11, 7, 5]), ("best", [6, 12, 10, 8]), ("for", [1, 2, 5])] == [1, 2, 5, 6, 7, 8, 10, 11, 12]
#guard extractUnique [("Built", [7, 1, 9, 4]), ("for", [11, 21, 36, 14, 9]), ("ISP", [4, 1, 21, 39, 47]), ("TV", [1, 32, 38])] == [1, 4, 7, 9, 11, 14, 21, 32, 36, 38, 39, 47]
#guard extractUnique [("F", [11, 13, 14, 17]), ("A", [12, 11, 15, 18]), ("N", [19, 21, 15, 36]), ("G", [37, 36, 35])] == [11, 12, 13, 14, 15, 17, 18, 19, 21, 35, 36, 37]
