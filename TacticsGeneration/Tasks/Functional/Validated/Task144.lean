import Batteries
open Std

def getAtD {α} (xs : List α) (i : Nat) (d : α) : α :=
  match xs.drop i with
  | [] => d
  | y :: _ => y

def sumPairs (arr : List Int) (n : Nat) : Int := Id.run do
  let mut s : Int := 0
  for i in [0 : n] do
    let j := (n - 1) - i
    let x := getAtD arr j 0
    let term := (Int.ofNat j) * x - (Int.ofNat i) * x
    s := s + term
  return s

#guard sumPairs [1, 8, 9, 15, 16] 5 = 74
#guard sumPairs [1, 2, 3, 4] 4 = 10
#guard sumPairs [1, 2, 3, 4, 5, 7, 9, 11, 14] 9 = 188
