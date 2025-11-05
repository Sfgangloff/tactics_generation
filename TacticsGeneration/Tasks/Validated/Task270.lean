import Batteries
open Std

def getAtDNat (xs : List Nat) (i d : Nat) : Nat :=
  match xs, i with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs', Nat.succ i' => getAtDNat xs' i' d

def sumEvenAndEvenIndex (arr : List Nat) (n : Nat) : Nat := Id.run do
  let mut s := 0
  let mut i := 0
  while i < n do
    let v := getAtDNat arr i 0
    if v % 2 == 0 then
      s := s + v
    i := i + 2
  return s

#guard sumEvenAndEvenIndex [5, 6, 12, 1, 18, 8] 6 = 30
#guard sumEvenAndEvenIndex [3, 20, 17, 9, 2, 10, 18, 13, 6, 18] 10 = 26
#guard sumEvenAndEvenIndex [5, 6, 12, 1] 4 = 12
