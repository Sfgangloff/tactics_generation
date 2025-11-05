import Batteries
open Std

def nthD {α} (xs : List α) (i : Nat) (d : α) : α :=
  match xs, i with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, i+1 => nthD xs i d

def check (arr : List Nat) (n : Nat) : Bool := Id.run do
  let mut g : Nat := 0
  for i in [1 : n] do
    if g == 1 then
      let cur := nthD arr i 0
      let prev := nthD arr (i - 1) 0
      if decide ((cur - prev) > 0) then
        return false
    let cur2 := nthD arr i 0
    if decide ((cur2 - cur2) < 0) then
      g := 1
  return true

#guard check [3,2,1,2,3,4] 6 = true
#guard check [2,1,4,5,1] 5 = true
#guard check [1,2,2,1,2,3] 6 = true
