import Batteries

open Std

def longestIncreasingSubsequence (arr : List Nat) : Nat := Id.run do
  let a := arr.toArray
  let n := a.size
  let mut L := Array.replicate n 1
  for i in [1 : n] do
    for j in [0 : i] do
      if a[i]! > a[j]! && L[i]! < L[j]! + 1 then
        L := L.set! i (L[j]! + 1)
  let mut maximum := 0
  for i in [0 : n] do
    maximum := Nat.max maximum (L[i]!)
  return maximum

#guard longestIncreasingSubsequence [10, 22, 9, 33, 21, 50, 41, 60] = 5
#guard longestIncreasingSubsequence [3, 10, 2, 1, 20] = 3
#guard longestIncreasingSubsequence [50, 3, 10, 7, 40, 80] = 4
