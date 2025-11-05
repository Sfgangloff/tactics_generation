import Batteries

open Std

def shellSort (my_list : List Nat) : List Nat := Id.run do
  let mut a := my_list.toArray
  let n := a.size
  let mut gap := n / 2
  while gap > 0 do
    for i in [gap : n] do
      let current_item := a[i]!
      let mut j := i
      while j >= gap do
        let prev := a[j - gap]!
        if prev > current_item then
          a := a.set! j prev
          j := j - gap
        else
          break
      a := a.set! j current_item
    gap := gap / 2
  return a.toList

#guard shellSort [12, 23, 4, 5, 3, 2, 12, 81, 56, 95] == [2, 3, 4, 5, 12, 12, 23, 56, 81, 95]
#guard shellSort [24, 22, 39, 34, 87, 73, 68] == [22, 24, 34, 39, 68, 73, 87]
#guard shellSort [32, 30, 16, 96, 82, 83, 74] == [16, 30, 32, 74, 82, 83, 96]
