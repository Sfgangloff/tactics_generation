import Batteries

open Std

def jacobsthalNum (n : Nat) : Nat := Id.run do
  let mut dp := Array.replicate (n+1) 0
  dp := dp.modify 0 (fun _ => 0)
  dp := dp.modify 1 (fun _ => 1)
  for i in [2 : n+1] do
    dp := dp.set! i <| dp[i-1]! + 2 * dp[i-2]!
  return dp[n]!

#guard jacobsthalNum 5 = 11
#guard jacobsthalNum 2 = 1
#guard jacobsthalNum 4 = 5
