import Batteries

open Std

def insertSorted {α} (le : α → α → Bool) (x : α) (l : List α) : List α :=
  match l with
  | [] => [x]
  | y :: ys => if le x y then x :: l else y :: insertSorted le x ys

def isort {α} (le : α → α → Bool) (l : List α) : List α :=
  l.foldr (fun a acc => insertSorted le a acc) []

def maxSumPairDiffLessthanK (arr : List Nat) (N K : Nat) : Nat := Id.run do
  let arrSorted := isort Nat.ble arr
  let arrA := arrSorted.toArray
  let mut dp := Array.replicate N 0
  
  for i in [1 : N] do
    dp := dp.set! i (dp[i-1]!)
    let ai := arrA[i]!
    let aim1 := arrA[i-1]!
    if Nat.blt (ai - aim1) K then
      let candidate := if Nat.ble 2 i then dp[i-2]! + ai + aim1 else ai + aim1
      let prev := dp[i]!
      let m := Nat.max prev candidate
      dp := dp.set! i m
  return dp[N-1]!

#guard maxSumPairDiffLessthanK [3, 5, 10, 15, 17, 12, 9] 7 4 = 62
#guard maxSumPairDiffLessthanK [5, 15, 10, 300] 4 12 = 25
#guard maxSumPairDiffLessthanK [1, 2, 3, 4, 5, 6] 6 6 = 21
