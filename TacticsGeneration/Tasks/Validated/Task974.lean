import Batteries

open Std

def minSumPath (A : List (List Nat)) : Nat := Id.run do
  let arr : Array (Array Nat) := A.toArray.map (fun row => row.toArray)
  if arr.size = 0 then
    return 0
  let n := arr.size - 1
  let last := arr[n]!
  let m := last.size
  
  let mut memo : Array Nat := Array.replicate arr.size 0
  
  for i in [0:m] do
    memo := memo.set! i (last[i]!)
  
  for k in [0 : arr.size - 1] do
    let i := (arr.size - 2) - k
    let row := arr[i]!
    let width := row.size
    for j in [0:width] do
      memo := memo.set! j (row[j]! + Nat.min (memo[j]!) (memo[j+1]!))
  return memo[0]!

#guard minSumPath [[2], [3, 9], [1, 6, 7]] == 6
#guard minSumPath [[2], [3, 7], [8, 5, 6]] == 10
#guard minSumPath [[3], [6, 4], [5, 2, 7]] == 9
