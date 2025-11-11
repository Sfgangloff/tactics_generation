import Batteries
open Std

def largestSubset (a : List Nat) (n : Nat) : Nat := Id.run do
  let aArr := a.toArray
  let mut dp := Array.replicate n 0
  if n == 0 then
    return 0
  dp := dp.set! (n - 1) 1
  let mut i := n - 1
  while i > 0 do
    let idx := i - 1
    let mut mxm := 0
    let ai := aArr[idx]!
    let mut j := i
    while j < n do
      let aj := aArr[j]!
      if aj % ai == 0 || ai % aj == 0 then
        let v := dp[j]!
        mxm := if mxm < v then v else mxm
      j := j + 1
    dp := dp.set! idx (1 + mxm)
    i := i - 1
  let mut res := 0
  for k in [: n] do
    let v := dp[k]!
    res := if res < v then v else res
  return res

#guard largestSubset [1, 3, 6, 13, 17, 18] 6 = 4
#guard largestSubset [10, 5, 3, 15, 20] 5 = 3
#guard largestSubset [18, 1, 3, 6, 13, 17] 6 = 4
