import Batteries

open Std

def hamming_Distance (n1 n2 : Nat) : Nat := Id.run do
  let mut x := n1 ^^^ n2
  let mut setBits := 0
  while x > 0 do
    setBits := setBits + (x &&& 1)
    x := x >>> 1
  return setBits

#guard hamming_Distance 4 8 = 2
#guard hamming_Distance 2 4 = 2
#guard hamming_Distance 1 2 = 2
