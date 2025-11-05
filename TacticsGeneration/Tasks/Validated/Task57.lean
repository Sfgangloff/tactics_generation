import Batteries

open Std

def findMaxNum (arr : List Nat) (n : Nat) : Nat :=
  let rec collectMaxNum (xs : List Nat) (acc : Nat) : Nat :=
    match xs with
    | [] => acc
    | x :: xs' => collectMaxNum xs' (acc * 10 + x)
  let maxList := Id.run do
    let mut result : List Nat := []
    let mut originalList := arr
    for _ in [0:n] do
      if originalList.isEmpty then break
      let maxDigit := originalList.foldl (init := 0) max
      result := result ++ [maxDigit]
      originalList := originalList.erase maxDigit
    return result
  collectMaxNum maxList 0

#guard findMaxNum [1, 2, 3] 3 == 321
#guard findMaxNum [4, 5, 6, 1] 4 == 6541
#guard findMaxNum [1, 2, 3, 9] 4 == 9321
