import Batteries

open Std

def List.get2d {α : Type} (l : List (List α)) (y x : Nat) (fallback : α) : α :=
  (l.getD y []).getD x fallback

def maxSumRectangularGrid (grid : List (List Nat)) (n : Nat) : Nat := Id.run do
  let mut incl := max (grid.get2d 0 0 0) (grid.get2d 1 0 0)
  let mut excl := 0
  for i in [1 : n] do
    let excl_new := max excl incl
    incl := excl + max (grid.get2d 0 i 0) (grid.get2d 1 i 0)
    excl := excl_new
  return max excl incl

#guard maxSumRectangularGrid [[1, 4, 5], [2, 0, 0]] 3 = 7
#guard maxSumRectangularGrid [[1, 2, 3, 4, 5], [6, 7, 8, 9, 10]] 5 = 24
#guard maxSumRectangularGrid [[7, 9, 11, 15, 19], [21, 25, 28, 31, 32]] 5 = 81
