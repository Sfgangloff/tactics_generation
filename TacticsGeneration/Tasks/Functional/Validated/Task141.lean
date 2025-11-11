import Batteries

open Std

def indexFirst (xs : List Nat) (v : Nat) : Nat :=
  let rec go (lst : List Nat) (i : Nat) : Nat :=
    match lst with
    | [] => 0
    | y :: ys => if y = v then i else go ys (i+1)
  go xs 0

def pancakeSort (nums : List Nat) : List Nat := Id.run do
  let mut nums := nums
  let mut arrLen := nums.length
  while arrLen > 1 do
    let pref := nums.take arrLen
    let m := pref.foldl Nat.max 0
    let mi := indexFirst nums m
    nums := (nums.take (mi+1)).reverse ++ nums.drop (mi+1)
    nums := (nums.take arrLen).reverse ++ nums.drop arrLen
    arrLen := arrLen - 1
  return nums

#guard pancakeSort [15, 79, 25, 38, 69] = [15, 25, 38, 69, 79]
#guard pancakeSort [98, 12, 54, 36, 85] = [12, 36, 54, 85, 98]
#guard pancakeSort [41, 42, 32, 12, 23] = [12, 23, 32, 41, 42]
