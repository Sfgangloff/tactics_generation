import Batteries

open Std

def testThreeEqual (x y z : Int) : Nat :=
  let s := (HashSet.empty.insert x).insert y |>.insert z
  let len := s.size
  if len == 3 then 0 else 4 - len

#guard testThreeEqual 1 1 1 = 3
#guard testThreeEqual (-1) (-2) (-3) = 0
#guard testThreeEqual 1 2 2 = 2
