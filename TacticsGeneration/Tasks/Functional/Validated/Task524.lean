import Batteries

open Std

def maxSumIncreasingSubsequence (arr : List Nat) (n : Nat) : Nat := Id.run do
  let a := arr.toArray
  let mut msis := Array.replicate n 0
  for i in [: n] do
    msis := msis.set! i (a.getD i 0)
  for i in [1 : n] do
    for j in [: i] do
      let ai := a.getD i 0
      let aj := a.getD j 0
      if ai > aj && msis[i]! < msis[j]! + ai then
        msis := msis.set! i (msis[j]! + ai)
  let mut m := 0
  for i in [: n] do
    if m < msis[i]! then
      m := msis[i]!
  return m

#guard maxSumIncreasingSubsequence [1, 101, 2, 3, 100, 4, 5] 7 = 106
#guard maxSumIncreasingSubsequence [3, 4, 5, 10] 4 = 22
#guard maxSumIncreasingSubsequence [10, 5, 4, 3] 4 = 10
