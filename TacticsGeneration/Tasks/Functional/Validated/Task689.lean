import Batteries
open Std

def minJumps (arr : List Nat) (n : Nat) : Nat := Id.run do
  let INF := n + 1
  if n == 0 then
    return INF
  let arrA := arr.toArray
  if arrA.getD 0 0 == 0 then
    return INF
  let mut jumps := Array.replicate n 0
  for i in [1 : n] do
    jumps := jumps.set! i INF
    let mut found := false
    for j in [0 : i] do
      if !found then
        let aj := arrA.getD j 0
        let cond1 := i ≤ j + aj
        let cond2 := jumps.getD j 0 != INF
        if cond1 && cond2 then
          let newv := Nat.min (jumps.getD i INF) ((jumps.getD j 0) + 1)
          jumps := jumps.set! i newv
          found := true
      else
        pure ()
  return jumps.getD (n - 1) INF

#guard minJumps [1, 3, 6, 1, 0, 9] 6 = 3
#guard minJumps [1, 3, 5, 8, 9, 2, 6, 7, 6, 8, 9] 11 = 3
#guard minJumps [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 11 = 10
