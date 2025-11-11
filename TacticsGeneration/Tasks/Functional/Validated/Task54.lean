import Batteries

open Std

def countingSort (my_list : List Nat) : List Nat := Id.run do
  let n := my_list.length
  let arrInput := my_list.toArray
  let mut maxVal := 0
  for idx in [: n] do
    let v := arrInput[idx]!
    if v > maxVal then
      maxVal := v
  let mut buckets := Array.replicate (maxVal + 1) 0
  for v in my_list do
    buckets := buckets.set! v (buckets[v]! + 1)
  let mut arr := arrInput
  let mut i := 0
  for j in [0 : maxVal + 1] do
    let count := buckets[j]!
    for _ in [: count] do
      arr := arr.set! i j
      i := i + 1
  return arr.toList

#guard countingSort [1, 23, 4, 5, 6, 7, 8] = [1, 4, 5, 6, 7, 8, 23]
#guard countingSort [12, 9, 28, 33, 69, 45] = [9, 12, 28, 33, 45, 69]
#guard countingSort [8, 4, 14, 3, 2, 1] = [1, 2, 3, 4, 8, 14]
