import Batteries

open Std

def findElement (arr : List Nat) (ranges : List (List Nat)) (rotations index : Nat) : Nat := Id.run do
  let mut idx := index
  for j in [0 : rotations] do
    let i := rotations - 1 - j
    let r := ranges.getD i []
    let left := r.getD 0 0
    let right := r.getD 1 0
    if left <= idx && right >= idx then
      if idx == left then
        idx := right
      else
        idx := idx - 1
  return arr.getD idx 0

#guard findElement [1,2,3,4,5] [[0,2],[0,3]] 2 1 = 3
#guard findElement [1,2,3,4] [[0,1],[0,2]] 1 2 = 3
#guard findElement [1,2,3,4,5,6] [[0,1],[0,2]] 1 1 = 1
