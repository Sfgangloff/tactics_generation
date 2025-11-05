import Batteries

open Std

def maxSumSubseq (A : List Nat) : Nat := Id.run do
  let n := A.length
  
  let arr := A.toArray
  if n == 1 then
    return arr[0]!
  let mut look := Array.replicate n 0
  look := look.set! 0 arr[0]!
  look := look.set! 1 (max arr[0]! arr[1]!)
  for i in [2 : n] do
    let v1 := look[i-1]!
    let v2 := look[i-2]! + arr[i]!
    let m := max v1 v2
    let m2 := max m arr[i]!
    look := look.set! i m2
  return look[n-1]!

#guard maxSumSubseq [1, 2, 9, 4, 5, 0, 4, 11, 6] = 26
#guard maxSumSubseq [1, 2, 9, 5, 6, 0, 5, 12, 7] = 28
#guard maxSumSubseq [1, 3, 10, 5, 6, 0, 6, 14, 21] = 44
