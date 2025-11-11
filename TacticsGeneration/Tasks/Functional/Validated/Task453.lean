import Batteries

open Std

def sumofFactors (n : Nat) : Nat := Id.run do
  if n % 2 != 0 then
    return 0
  let mut nVar := n
  let mut res := 1
  let limit := Nat.sqrt nVar
  for i in [2 : limit + 1] do
    let mut count := 0
    let mut currSum := 1
    let mut currTerm := 1
    while nVar % i == 0 do
      count := count + 1
      nVar := nVar / i
      if i == 2 && count == 1 then
        currSum := 0
      currTerm := currTerm * i
      currSum := currSum + currTerm
    res := res * currSum
  res := res * (if nVar >= 2 then 1 + nVar else 1)
  return res

#guard sumofFactors 18 = 26
#guard sumofFactors 30 = 48
#guard sumofFactors 6 = 8
