import Batteries
open Std

def numDigits (n : Nat) : Nat :=
  let rec aux (k m : Nat) : Nat :=
    match k with
    | 0 => 0
    | k+1 =>
      if m < 10 then 1 else 1 + aux k (m / 10)
  aux (n + 1) n

def tupleToFloat (testTup : Nat × Nat) : Float :=
  let a := testTup.fst
  let b := testTup.snd
  let k := numDigits b
  (Float.ofNat a) + (Float.ofNat b) / (Float.ofNat (Nat.pow 10 k))

#guard tupleToFloat (4, 56) == 4.56
#guard tupleToFloat (7, 256) == 7.256
#guard tupleToFloat (8, 123) == 8.123
