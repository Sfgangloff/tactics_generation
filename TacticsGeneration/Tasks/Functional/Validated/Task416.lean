import Batteries

open Std

def MAX : Nat := 1000000

def breakSum (n : Nat) : Nat := Id.run do
  let mut dp := Array.replicate (n+1) 0
  dp := dp.set! 0 0
  dp := dp.set! 1 1
  for i in [2 : n+1] do
    let v := max (dp[i/2]! + dp[i/3]! + dp[i/4]!) i
    dp := dp.set! i v
  return dp[n]!

#guard breakSum 12 = 13
#guard breakSum 24 = 27
#guard breakSum 23 = 23
