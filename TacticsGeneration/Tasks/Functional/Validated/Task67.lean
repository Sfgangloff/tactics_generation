import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) : Array (Array α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) : Array (Array α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) : α :=
  (a.getD y #[]).getD x fallback

def bellNumber (n : Nat) : Nat := Id.run do
  let size := n + 1
  let mut bell : Array (Array Nat) := Array.replicate size (Array.replicate size 0)
  bell := bell.set2d? 0 0 1
  for i in [1 : n+1] do
    bell := bell.set2d? i 0 (bell.get2d (i-1) (i-1) 0)
    for j in [1 : i+1] do
      let v := bell.get2d (i-1) (j-1) 0 + bell.get2d i (j-1) 0
      bell := bell.set2d? i j v
  return bell.get2d n 0 0

#guard bellNumber 2 == 2
#guard bellNumber 10 == 115975
#guard bellNumber 56 == 6775685320645824322581483068371419745979053216268760300
