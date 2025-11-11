import Batteries

open Std

def getInvCount (arr : List Nat) (n : Nat) : Nat := Id.run do
  let mut invCount := 0
  for i in [: n] do
    for j in [i+1 : n] do
      let ai := arr.getD i 0
      let aj := arr.getD j 0
      if Nat.blt aj ai then
        invCount := invCount + 1
  return invCount

#guard getInvCount [1, 20, 6, 4, 5] 5 = 5
#guard getInvCount [8, 4, 2, 1] 4 = 6
#guard getInvCount [3, 1, 2] 3 = 2
