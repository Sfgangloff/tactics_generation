import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def coinChange (S : List Nat) (m n : Nat) : Nat := Id.run do
  let mut table : Array (Array Nat) := Array.replicate (n+1) (Array.replicate m 0)
  
  for j in [: m] do
    table := table.set2d? 0 j 1
  
  for i in [1 : n+1] do
    for j in [: m] do
      let coin := S.getD j 0
      let x := if i >= coin then table.get2d (i - coin) j 0 else 0
      let y := if j >= 1 then table.get2d i (j-1) 0 else 0
      table := table.set2d? i j (x + y)
  return table.get2d n (m-1) 0

#guard coinChange [1, 2, 3] 3 4 = 4
#guard coinChange [4, 5, 6, 7, 8, 9] 6 9 = 2
#guard coinChange [4, 5, 6, 7, 8, 9] 6 4 = 1
