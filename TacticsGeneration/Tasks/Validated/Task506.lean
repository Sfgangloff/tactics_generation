import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def permutationCoefficient (n k : Nat) : Nat := Id.run do
  let mut P : Array (Array Nat) := Array.replicate (n+1) (Array.replicate (k+1) 0)
  for i in [0 : n+1] do
    let m := Nat.min i k
    for j in [0 : m+1] do
      if j == 0 then
        P := P.set2d? i j 1
      else
        let v := P.get2d (i-1) j 0 + j * P.get2d (i-1) (j-1) 0
        P := P.set2d? i j v
      if j < k then
        P := P.set2d? i (j+1) 0
  return P.get2d n k 0

#guard permutationCoefficient 10 2 = 90
#guard permutationCoefficient 10 3 = 720
#guard permutationCoefficient 10 1 = 10
