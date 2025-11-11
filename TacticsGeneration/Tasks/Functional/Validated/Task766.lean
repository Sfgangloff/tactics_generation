import Batteries

open Std

def pairWise (l1 : List Nat) : List (Nat × Nat) := Id.run do
  let mut temp : Array (Nat × Nat) := #[]
  let n := l1.length
  for i in [: n - 1] do
    let current_element := l1.getD i 0
    let next_element := l1.getD (i + 1) 0
    let x := (current_element, next_element)
    temp := temp.push x
  return temp.toList

#guard pairWise [1,1,2,3,3,4,4,5] = [(1, 1), (1, 2), (2, 3), (3, 3), (3, 4), (4, 4), (4, 5)]
#guard pairWise [1,5,7,9,10] = [(1, 5), (5, 7), (7, 9), (9, 10)]
#guard pairWise [1,2,3,4,5,6,7,8,9,10] = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10)]
