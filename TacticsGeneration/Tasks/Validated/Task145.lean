import Batteries
open Std

def maxAbsDiff (arr : List Nat) (n : Nat) : Nat :=
  let l := arr.take n
  match l with
  | [] => 0
  | x :: xs =>
    let (mn, mx) :=
      xs.foldl
        (fun (mnmx : Nat × Nat) z =>
          let mn := mnmx.fst
          let mx := mnmx.snd
          (Nat.min mn z, Nat.max mx z))
        (x, x)
    mx - mn

#guard maxAbsDiff [2,1,5,3] 4 = 4
#guard maxAbsDiff [9,3,2,5,1] 5 = 8
#guard maxAbsDiff [3,2,1] 3 = 2
