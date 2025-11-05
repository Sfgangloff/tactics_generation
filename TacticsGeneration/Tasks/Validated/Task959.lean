import Batteries

open Std

def Average (lst : List Nat) : Float :=
  let s := lst.foldl (fun acc x => acc + x) 0
  Float.ofNat s / Float.ofNat lst.length

#guard Average [15, 9, 55, 41, 35, 20, 62, 49] == 35.75
#guard Average [4, 5, 1, 2, 9, 7, 10, 8] == 5.75
#guard Average [1, 2, 3] == 2.0
