import Batteries

open Std

def find_Points (l1 r1 l2 r2 : Int) : Int × Int :=
  let x := if l1 != l2 then (if l1 ≤ l2 then l1 else l2) else (-1)
  let y := if r1 != r2 then (if r1 ≥ r2 then r1 else r2) else (-1)
  (x, y)

#guard find_Points 5 10 1 5 = (1, 10)
#guard find_Points 3 5 7 9 = (3, 9)
#guard find_Points 1 5 2 8 = (1, 8)
