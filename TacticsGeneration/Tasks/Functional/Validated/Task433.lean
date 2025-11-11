import Batteries

open Std

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if Nat.ble x y then x :: y :: ys else y :: insertNat x ys

def isortNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (isortNat xs)

def lastNatD (xs : List Nat) (d : Nat) : Nat :=
  match xs with
  | [] => d
  | [x] => x
  | _ :: xs' => lastNatD xs' d

def check_greater (arr : List Nat) (number : Nat) : String :=
  let arrSorted := isortNat arr
  let last := lastNatD arrSorted 0
  if number > last then
    "Yes, the entered number is greater than those in the array"
  else
    "No, entered number is less than those in the array"

#guard check_greater [1, 2, 3, 4, 5] 4 == "No, entered number is less than those in the array"
#guard check_greater [2, 3, 4, 5, 6] 8 == "Yes, the entered number is greater than those in the array"
#guard check_greater [9, 7, 4, 8, 6, 1] 11 == "Yes, the entered number is greater than those in the array"
