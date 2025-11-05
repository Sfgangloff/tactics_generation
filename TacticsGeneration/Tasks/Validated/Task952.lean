import Batteries

open Std

def nCr_mod_p (n r p : Nat) : Nat := Id.run do
  let r := if r > n - r then n - r else r
  let mut C := Array.replicate (r + 1) 0
  C := C.set! 0 1
  for i in [1 : n + 1] do
    let maxJ := min i r
    for t in [0 : maxJ] do
      let j := maxJ - t
      let val := (C[j]! + C[j - 1]!) % p
      C := C.set! j val
  return C[r]!

#guard nCr_mod_p 10 2 13 == 6
#guard nCr_mod_p 11 3 14 == 11
#guard nCr_mod_p 18 14 19 == 1
