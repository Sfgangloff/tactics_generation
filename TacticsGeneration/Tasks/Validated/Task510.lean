import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def noOfSubsequences (arr : List Nat) (k : Nat) : Nat := Id.run do
  let n := arr.length
  let mut dp : Array (Array Nat) := Array.replicate (k+1) (Array.replicate (n+1) 0)
  for i in [1 : k + 1] do
    for j in [1 : n + 1] do
      let base := dp.get2d i (j-1) 0
      let a := arr.getD (j-1) 0
      let val :=
        if h : a ≤ i ∧ a > 0 then
          base + (dp.get2d (i / a) (j-1) 0 + 1)
        else
          base
      dp := dp.set2d? i j val
  return dp.get2d k n 0

#guard noOfSubsequences [1,2,3,4] 10 = 11
#guard noOfSubsequences [4,8,7,2] 50 = 9
#guard noOfSubsequences [5,6,7,8] 15 = 4
