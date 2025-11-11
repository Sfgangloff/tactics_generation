import Batteries

open Std

def jacobsthalLucas (n : Nat) : Nat := Id.run do
  
  let mut dp := Array.replicate (n+1) 0
  dp := dp.modify 0 (fun _ => 2)
  dp := dp.modify 1 (fun _ => 1)
  for i in [2 : n+1] do
    dp := dp.set! i <| dp[i-1]! + 2 * dp[i-2]!
  return dp[n]!

#guard jacobsthalLucas 5 == 31
#guard jacobsthalLucas 2 == 5
#guard jacobsthalLucas 4 == 17
