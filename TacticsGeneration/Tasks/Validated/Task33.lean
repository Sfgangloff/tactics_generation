import Batteries

open Std

def decimalToBinary (N : Nat) : Nat := Id.run do
  let mut N := N
  let mut bNumber : Nat := 0
  let mut cnt : Nat := 0
  while N != 0 do
    let rem := N % 2
    let c := Nat.pow 10 cnt
    bNumber := bNumber + rem * c
    N := N / 2
    cnt := cnt + 1
  return bNumber

#guard decimalToBinary 10 = 1010
#guard decimalToBinary 1 = 1
#guard decimalToBinary 20 = 10100
