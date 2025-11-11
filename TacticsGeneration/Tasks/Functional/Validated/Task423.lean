import Batteries
open Std

def modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def get2d {α : Type} (l : List (List α)) (y x : Nat) (fallback : α) :=
  (l.getD y []).getD x fallback

def get_maxgold (gold : List (List Nat)) (m n : Nat) : Nat := Id.run do
  let mut goldTable : Array (Array Nat) := Array.replicate m (Array.replicate n 0)
  
  for c in [0 : n] do
    let col := n - 1 - c
    for row in [0 : m] do
      let right := if col == n - 1 then 0 else goldTable.get2d row (col+1) 0
      let right_up := if row == 0 || col == n - 1 then 0 else goldTable.get2d (row-1) (col+1) 0
      let right_down := if row == m - 1 || col == n - 1 then 0 else goldTable.get2d (row+1) (col+1) 0
      let best := Nat.max (Nat.max right right_up) right_down
      let val := gold.get2d row col 0 + best
      goldTable := goldTable.set2d? row col val
  let mut res := goldTable.get2d 0 0 0
  for i in [1 : m] do
    res := Nat.max res (goldTable.get2d i 0 0)
  return res

#guard get_maxgold [[1, 3, 1, 5],[2, 2, 4, 1],[5, 0, 2, 3],[0, 6, 1, 2]] 4 4 = 16
#guard get_maxgold [[10,20],[30,40]] 2 2 = 70
#guard get_maxgold [[4,9],[3,7]] 2 2 = 13
