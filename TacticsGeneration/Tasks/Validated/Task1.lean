import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y <| fun row => row.modify x f

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def List.get2d {α : Type} (l : List (List α)) (y x : Nat) (fallback : α) :=
  (l.getD y []).getD x fallback

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def minCost (cost : List (List Nat)) (m n : Nat) : Nat := Id.run do
  let mut tc : Array (Array Nat) :=
    Array.replicate (m+1) (Array.replicate (n+1) 0)
  tc := tc.set2d? 0 0 (cost.get2d 0 0 0)
  for i in [1 : m+1] do
    tc := tc.set2d? i 0 <| tc.get2d (i-1) 0 0 + cost.get2d i 0 0
  for j in [1 : n+1] do
    tc := tc.set2d? 0 j <| tc.get2d 0 (j-1) 0 + cost.get2d 0 j 0
  for i in [1 : m+1] do
    for j in [1 : n+1] do
      tc := tc.set2d? i j <|
        min (tc.get2d (i-1) (j-1) 0) (
          min (tc.get2d (i-1) j 0) (tc.get2d i (j-1) 0)
        ) + cost.get2d i j 0
  return tc.get2d m n 0

#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16
