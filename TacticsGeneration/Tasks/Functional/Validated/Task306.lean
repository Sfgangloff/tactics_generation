import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def maxSumIncreasingSubseq (a : List Nat) (n index k : Nat) : Nat := Id.run do
  let mut dp : Array (Array Nat) := Array.replicate n (Array.replicate n 0)
  
  let a0 := a.getD 0 0
  for i in [: n] do
    let ai := a.getD i 0
    let v := if ai > a0 then ai + a0 else ai
    dp := dp.set2d? 0 i v
  
  for i in [1 : n] do
    for j in [: n] do
      let ai := a.getD i 0
      let aj := a.getD j 0
      if aj > ai && j > i then
        let v1 := dp.get2d (i-1) i 0 + aj
        let v2 := dp.get2d (i-1) j 0
        let v := if v1 > v2 then v1 else v2
        dp := dp.set2d? i j v
      else
        let v2 := dp.get2d (i-1) j 0
        dp := dp.set2d? i j v2
  return dp.get2d index k 0

#guard maxSumIncreasingSubseq [1, 101, 2, 3, 100, 4, 5] 7 4 6 = 11
#guard maxSumIncreasingSubseq [1, 101, 2, 3, 100, 4, 5] 7 2 5 = 7
#guard maxSumIncreasingSubseq [11, 15, 19, 21, 26, 28, 31] 7 2 4 = 71
