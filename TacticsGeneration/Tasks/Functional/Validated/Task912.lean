import Batteries

open Std

def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def binomialCoeff (n k : Nat) : Nat := Id.run do
  let mut C : Array (Array Nat) := Array.replicate (n+1) (Array.replicate (k+1) 0)
  for i in [0 : n+1] do
    let upto := min i k
    for j in [0 : upto+1] do
      if j == 0 || j == i then
        C := C.set2d? i j 1
      else
        let val := C.get2d (i-1) (j-1) 0 + C.get2d (i-1) j 0
        C := C.set2d? i j val
  return C.get2d n k 0

def lobbNum (n m : Nat) : Nat :=
  ((2 * m + 1) * binomialCoeff (2 * n) (m + n)) / (m + n + 1)

#guard lobbNum 5 3 = 35
#guard lobbNum 3 2 = 5
#guard lobbNum 4 2 = 20
