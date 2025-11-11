import Batteries

open Std

def countNoOfWays (n k : Nat) : Nat := Id.run do
  let mut dp := Array.replicate (n+1) 0
  let modv := 1000000007
  dp := dp.modify 1 (fun _ => k)
  dp := dp.modify 2 (fun _ => k * k)
  for i in [3 : n+1] do
    dp := dp.set! i (((k - 1) * (dp[i-1]! + dp[i-2]!)) % modv)
  return dp[n]!

#guard countNoOfWays 2 4 = 16
#guard countNoOfWays 3 2 = 6
#guard countNoOfWays 4 4 = 228
