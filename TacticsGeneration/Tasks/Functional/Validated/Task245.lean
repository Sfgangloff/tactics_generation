import Batteries
open Std

def maxSum (arr : List Int) (n : Nat) : Int := Id.run do
  let arrA := arr.toArray
  let mut MSIBS := arrA
  let mut MSDBS := arrA
  
  for i in [0 : n] do
    for j in [0 : i] do
      let ai := arrA.getD i 0
      let aj := arrA.getD j 0
      let cur := MSIBS.getD i 0
      let cand := (MSIBS.getD j 0) + ai
      if ai > aj && cur < cand then
        MSIBS := MSIBS.set! i cand
  
  for i in [1 : n + 1] do
    for j in [1 : i] do
      let ii := n - i
      let jj := n - j
      let ai := arrA.getD ii 0
      let aj := arrA.getD jj 0
      let cur := MSDBS.getD ii 0
      let cand := (MSDBS.getD jj 0) + ai
      if ai > aj && cur < cand then
        MSDBS := MSDBS.set! ii cand
  
  let mut m : Int := 0
  if n > 0 then
    let v0 := (MSIBS.getD 0 0) + (MSDBS.getD 0 0) - (arrA.getD 0 0)
    m := v0
  for i in [0 : n] do
    let val := (MSIBS.getD i 0) + (MSDBS.getD i 0) - (arrA.getD i 0)
    if val > m then m := val
  return m

#guard maxSum [1, 15, 51, 45, 33, 100, 12, 18, 9] 9 = 194
#guard maxSum [80, 60, 30, 40, 20, 10] 6 = 210
#guard maxSum [2, 3, 14, 16, 21, 23, 29, 30] 8 = 138
