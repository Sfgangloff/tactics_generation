import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def find_longest_repeating_subseq (str : String) : Nat := Id.run do
  let n := str.length
  let mut dp : Array (Array Nat) := Array.replicate (n+1) (Array.replicate (n+1) 0)
  for i in [1 : n+1] do
    for j in [1 : n+1] do
      let ci := (str.drop (i-1)).take 1
      let cj := (str.drop (j-1)).take 1
      let value :=
        if ci == cj && i != j then
          1 + dp.get2d (i-1) (j-1) 0
        else
          Nat.max (dp.get2d i (j-1) 0) (dp.get2d (i-1) j 0)
      dp := dp.set2d? i j value
  return dp.get2d n n 0

#guard find_longest_repeating_subseq "AABEBCDD" = 3
#guard find_longest_repeating_subseq "aabb" = 2
#guard find_longest_repeating_subseq "aab" = 1
