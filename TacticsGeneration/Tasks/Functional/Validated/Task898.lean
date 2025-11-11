import Batteries

open Std

def extractElements (numbers : List Nat) (n : Nat) : List Nat :=
  let rec loop (lst : List Nat) (curVal : Option Nat) (curCount : Nat) (acc : List Nat) : List Nat :=
    match lst with
    | [] =>
      let acc := match curVal with
        | some v => if curCount == n then v :: acc else acc
        | none => acc
      acc.reverse
    | x :: xs =>
      match curVal with
      | none => loop xs (some x) 1 acc
      | some v =>
        if x == v then
          loop xs (some v) (curCount + 1) acc
        else
          let acc := if curCount == n then v :: acc else acc
          loop xs (some x) 1 acc
  loop numbers none 0 []

#guard extractElements [1, 1, 3, 4, 4, 5, 6, 7] 2 == [1, 4]
#guard extractElements [0, 1, 2, 3, 4, 4, 4, 4, 5, 7] 4 == [4]
#guard extractElements [0, 0, 0, 0, 0] 5 == [0]
