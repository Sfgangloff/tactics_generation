import Batteries
open Std

def getMaxOccuringChar (str1 : String) : String := Id.run do
  let mut ctr : List (Char × Nat) := []
  let mut maxVal : Nat := 0
  let mut ch : String := ""
  for c in str1.data do
    let rec inc (xs : List (Char × Nat)) : List (Char × Nat) :=
      match xs with
      | [] => [(c, 1)]
      | (c', n) :: xs' =>
        if c' = c then
          (c, n + 1) :: xs'
        else
          (c', n) :: inc xs'
    ctr := inc ctr
  for c in str1.data do
    let rec lookup (xs : List (Char × Nat)) : Nat :=
      match xs with
      | [] => 0
      | (c', n) :: xs' =>
        if c' = c then n else lookup xs'
    let count := lookup ctr
    if maxVal < count then
      maxVal := count
      ch := String.singleton c
  return ch

#guard getMaxOccuringChar "data" == "a"
#guard getMaxOccuringChar "create" == "e"
#guard getMaxOccuringChar "brilliant girl" == "i"
