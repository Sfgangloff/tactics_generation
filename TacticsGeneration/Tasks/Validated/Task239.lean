import Batteries
open Std

def modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :
    Array (Array α) :=
  a.modify y (fun row => row.modify x f)

def set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :
    Array (Array α) :=
  a.modify2d y x (fun _ => value)

def get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) : α :=
  (a.getD y #[]).getD x fallback

def get_total_number_of_sequences (m n : Nat) : Nat := Id.run do
  let mut T : Array (Array Nat) := Array.replicate (m+1) (Array.replicate (n+1) 0)
  for i in [0 : m+1] do
    for j in [0 : n+1] do
      let val :=
        if i == 0 || j == 0 then 0
        else if i < j then 0
        else if j == 1 then i
        else
          let a := T.get2d (i-1) j 0
          let b := T.get2d (i / 2) (j-1) 0
          a + b
      T := T.set2d? i j val
  return T.get2d m n 0

#guard get_total_number_of_sequences 10 4 = 4
#guard get_total_number_of_sequences 5 2 = 6
#guard get_total_number_of_sequences 16 3 = 84
