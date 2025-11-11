import Batteries

open Std

def maxProfit (price : List Int) (k : Nat) : Int := Id.run do
  let pr := price.toArray
  let n := pr.size
  if n == 0 then
    return 0
  let mut fp : Array (Array Int) := Array.replicate (k+1) (Array.replicate n 0)
  for i in [0 : k+1] do
    for j in [0 : n] do
      if i == 0 || j == 0 then
        fp := fp.modify i (fun row => row.set! j 0)
      else
        let rowPrev := fp[i-1]!
        let rowI := fp[i]!
        let mut maxSoFar : Int := 0
        for x in [0 : j] do
          let curr := pr[j]! - pr[x]! + rowPrev[x]!
          if maxSoFar < curr then
            maxSoFar := curr
        let left := rowI[j-1]!
        let val := if left < maxSoFar then maxSoFar else left
        fp := fp.modify i (fun row => row.set! j val)
  return fp[k]![n-1]!

#guard maxProfit [1, 5, 2, 3, 7, 6, 4, 5] 3 = 10
#guard maxProfit [2, 4, 7, 5, 4, 3, 5] 2 = 7
#guard maxProfit [10, 6, 8, 4, 2] 2 = 2
