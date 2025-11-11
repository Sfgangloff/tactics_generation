import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def List.get2d {α : Type} (l : List (List α)) (y x : Nat) (fallback : α) :=
  (l.getD y []).getD x fallback

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def maxAverageOfPath (cost : List (List Nat)) (N : Nat) : Float := Id.run do
  let mut dp : Array (Array Nat) := Array.replicate (N+1) (Array.replicate (N+1) 0)
  dp := dp.set2d? 0 0 (cost.get2d 0 0 0)
  for i in [1 : N] do
    dp := dp.set2d? i 0 <| dp.get2d (i-1) 0 0 + cost.get2d i 0 0
  for j in [1 : N] do
    dp := dp.set2d? 0 j <| dp.get2d 0 (j-1) 0 + cost.get2d 0 j 0
  for i in [1 : N] do
    for j in [1 : N] do
      let best := max (dp.get2d (i-1) j 0) (dp.get2d i (j-1) 0)
      dp := dp.set2d? i j <| best + cost.get2d i j 0
  let total := dp.get2d (N-1) (N-1) 0
  let numerator := Float.ofNat total
  let denomNat := 2 * N - 1
  let denom := Float.ofNat denomNat
  return numerator / denom

#guard maxAverageOfPath [[1, 2, 3], [6, 5, 4], [7, 3, 9]] 3 == (5.2 : Float)
#guard maxAverageOfPath [[2, 3, 4], [7, 6, 5], [8, 4, 10]] 3 == (6.2 : Float)
#guard maxAverageOfPath [[3, 4, 5], [8, 7, 6], [9, 5, 11]] 3 == (7.2 : Float)
