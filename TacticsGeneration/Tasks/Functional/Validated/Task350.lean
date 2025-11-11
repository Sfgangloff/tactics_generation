import Batteries

open Std

def minimum_Length (s : String) : Nat := Id.run do
  let n := s.length
  let mut maxOcc := 0
  let mut arr : Array Nat := Array.replicate 26 0
  for c in s.data do
    let cn := c.toNat
    let an := ('a' : Char).toNat
    let zn := ('z' : Char).toNat
    if an ≤ cn && cn ≤ zn then
      let i := cn - an
      arr := arr.set! i (arr[i]! + 1)
    else
      ()
  for i in [0:26] do
    let v := arr[i]!
    if v > maxOcc then
      maxOcc := v
  return n - maxOcc

#guard minimum_Length "mnm" = 1
#guard minimum_Length "abcda" = 3
#guard minimum_Length "abcb" = 2
