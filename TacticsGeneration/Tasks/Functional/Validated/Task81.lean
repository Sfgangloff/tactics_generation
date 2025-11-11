import Batteries

open Std

def zipTuples (test_tup1 : List Nat) (test_tup2 : List Nat) : List (Nat × Nat) := Id.run do
  
  let a1 := test_tup1.toArray
  let a2 := test_tup2.toArray
  let len2 := a2.size
  let mut res : Array (Nat × Nat) := #[]
  for i in [0 : a1.size] do
    let j := a1[i]!
    let idx := i % len2
    let k := a2[idx]!
    res := res.push (j, k)
  return res.toList

#guard zipTuples [7, 8, 4, 5, 9, 10] [1, 5, 6] = [(7, 1), (8, 5), (4, 6), (5, 1), (9, 5), (10, 6)]
#guard zipTuples [8, 9, 5, 6, 10, 11] [2, 6, 7] = [(8, 2), (9, 6), (5, 7), (6, 2), (10, 6), (11, 7)]
#guard zipTuples [9, 10, 6, 7, 11, 12] [3, 7, 8] = [(9, 3), (10, 7), (6, 8), (7, 3), (11, 7), (12, 8)]
