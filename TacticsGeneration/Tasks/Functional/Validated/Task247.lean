import Batteries
open Std

def modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :
    Array (Array α) :=
  a.modify y (fun row => row.modify x f)

def set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :
    Array (Array α) :=
  a.modify2d y x (fun _ => value)

def get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :
    α :=
  (a.getD y #[]).getD x fallback

def lps (str : String) : Nat := Id.run do
  let chars := str.data.toArray
  let n := chars.size
  if n = 0 then
    return 0
  let mut L : Array (Array Nat) := Array.replicate n (Array.replicate n 0)
  
  for i in [: n] do
    L := L.set2d? i i 1
  
  for cl in [2 : n + 1] do
    
    for i in [: (n - cl + 1)] do
      let j := i + cl - 1
      let ci := chars[i]!
      let cj := chars[j]!
      if ci == cj && cl == 2 then
        L := L.set2d? i j 2
      else if ci == cj then
        let v := L.get2d (i+1) (j-1) 0 + 2
        L := L.set2d? i j v
      else
        let a := L.get2d i (j-1) 0
        let b := L.get2d (i+1) j 0
        L := L.set2d? i j (max a b)
  return L.get2d 0 (n-1) 0

#guard lps "TENS FOR TENS" == 5
#guard lps "CARDIO FOR CARDS" == 7
#guard lps "PART OF THE JOURNEY IS PART" == 9
