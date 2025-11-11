import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def maxPathSum (tri : List (List Nat)) (m n : Nat) : Nat := Id.run do
  let mut a : Array (Array Nat) := tri.toArray.map (fun row => row.toArray)
  
  for di in [0 : m] do
    let i := (m - 1) - di
    
    for j in [0 : i + 1] do
      let below := a.get2d (i+1) j 0
      let belowRight := a.get2d (i+1) (j+1) 0
      let chosen := if below > belowRight then below else belowRight
      let current := a.get2d i j 0
      a := a.set2d? i j (current + chosen)
  return a.get2d 0 0 0

#guard maxPathSum [[1, 0, 0], [4, 8, 0], [1, 5, 3]] 2 2 = 14
#guard maxPathSum [[13, 0, 0], [7, 4, 0], [2, 4, 6]] 2 2 = 24
#guard maxPathSum [[2, 0, 0], [11, 18, 0], [21, 25, 33]] 2 2 = 53
