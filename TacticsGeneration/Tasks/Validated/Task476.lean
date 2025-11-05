import Batteries

open Std

def bigSum (nums : List Int) : Int :=
  
  match nums with
  | [] => 0
  | x :: xs =>
    let mx := xs.foldl (fun acc v => if acc < v then v else acc) x
    let mn := xs.foldl (fun acc v => if v < acc then v else acc) x
    mx + mn

#guard bigSum [1, 2, 3] = 4
#guard bigSum [-1, 2, 3, 4] = 3
#guard bigSum [2, 3, 6] = 8
