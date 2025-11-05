import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def bellNumber (n : Nat) : Nat := Id.run do
  let mut bell : Array (Array Nat) := Array.replicate (n+1) (Array.replicate (n+1) 0)
  bell := bell.set2d? 0 0 1
  for i in [1 : n+1] do
    bell := bell.set2d? i 0 (bell.get2d (i-1) (i-1) 0)
    for j in [1 : i+1] do
      bell := bell.set2d? i j (bell.get2d (i-1) (j-1) 0 + bell.get2d i (j-1) 0)
  return bell.get2d n 0 0

#guard bellNumber 2 = 2
#guard bellNumber 3 = 5
#guard bellNumber 4 = 15
