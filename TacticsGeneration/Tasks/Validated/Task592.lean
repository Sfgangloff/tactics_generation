import Batteries

open Std

def binomialCoeff (n k : Nat) : Nat := Id.run do
  let mut C : Array Nat := Array.replicate (k+1) 0
  C := C.set! 0 1
  for i in [1 : n+1] do
    let upper := Nat.min i k
    let mut j := upper
    while h : j > 0 do
      let vj := C[j]!
      let vjm1 := C[j-1]!
      C := C.set! j (vj + vjm1)
      j := j - 1
  return C[k]!

def sumOfProduct (n : Nat) : Nat :=
  binomialCoeff (2 * n) (n - 1)

#guard sumOfProduct 3 == 15
#guard sumOfProduct 4 == 56
#guard sumOfProduct 1 == 1
