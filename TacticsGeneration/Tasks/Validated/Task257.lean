import Batteries

open Std

def swapNumbers (a b : Nat) : Nat × Nat := Id.run do
  let mut a := a
  let mut b := b
  let temp := a
  a := b
  b := temp
  return (a, b)

#guard swapNumbers 10 20 = (20, 10)
#guard swapNumbers 15 17 = (17, 15)
#guard swapNumbers 100 200 = (200, 100)
