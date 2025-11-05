import Batteries

open Std

def findMaxVal (n x y : Nat) : Int := Id.run do
  let mut ans : Int := -1  
  for k in [0 : n+1] do
    if k % x == y then
      let kk : Int := Int.ofNat k
      if kk > ans then
        ans := kk
  if ans >= 0 && ans ≤ Int.ofNat n then
    return ans
  else
    return -1

#guard findMaxVal 15 10 5 == (15 : Int)
#guard findMaxVal 187 10 5 == (185 : Int)
#guard findMaxVal 16 11 1 == (12 : Int)
