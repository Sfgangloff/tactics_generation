import Batteries

open Std

def maximumSegments (n a b c : Nat) : Int := Id.run do
  let mut dp : Array Int := Array.replicate (n + 10) (-1)
  dp := dp.set! 0 0
  for i in [0 : n] do
    if dp[i]! != (-1) then
      if h₁ : i + a ≤ n then
        let cand := dp[i]! + 1
        let cur := dp[i + a]!
        let mx := max cand cur
        dp := dp.set! (i + a) mx
      else
        pure ()
      if h₂ : i + b ≤ n then
        let cand := dp[i]! + 1
        let cur := dp[i + b]!
        let mx := max cand cur
        dp := dp.set! (i + b) mx
      else
        pure ()
      if h₃ : i + c ≤ n then
        let cand := dp[i]! + 1
        let cur := dp[i + c]!
        let mx := max cand cur
        dp := dp.set! (i + c) mx
      else
        pure ()
  return dp[n]!

#guard maximumSegments 7 5 2 5 = (2 : Int)
#guard maximumSegments 17 2 1 3 = (17 : Int)
#guard maximumSegments 18 16 3 6 = (6 : Int)
