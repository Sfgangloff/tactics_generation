import Batteries

open Std

def increasingTrend (nums : List Nat) : Bool :=
  match nums with
  | [] => true
  | x :: xs =>
    let rec go (prev : Nat) (ys : List Nat) : Bool :=
      match ys with
      | [] => true
      | y :: ys' => if prev ≤ y then go y ys' else false
    go x xs

#guard increasingTrend [1, 2, 3, 4] = true
#guard increasingTrend [4, 3, 2, 1] = false
#guard increasingTrend [0, 1, 4, 9] = true
