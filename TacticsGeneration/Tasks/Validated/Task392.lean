import Batteries

open Std

def getMaxSum (n : Nat) : Nat := Id.run do
  let mut res := Array.replicate (n+1) 0
  for i in [0 : n+1] do
    if i == 0 then
      res := res.set! i 0
    else if i == 1 then
      res := res.set! i 1
    else
      let v := res[(i / 2)]! + res[(i / 3)]! + res[(i / 4)]! + res[(i / 5)]!
      let m := Nat.max i v
      res := res.set! i m
  return res[n]!

#guard getMaxSum 60 = 106
#guard getMaxSum 10 = 12
#guard getMaxSum 2 = 2
