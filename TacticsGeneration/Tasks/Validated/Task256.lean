import Batteries

open Std

def countPrimesNums (n : Nat) : Nat := Id.run do
  let mut ctr := 0
  for num in [0 : n] do
    if num <= 1 then continue
    let mut isPrime := true
    for i in [2 : num] do
      if num % i == 0 then
        isPrime := false
        break
    if isPrime then
      ctr := ctr + 1
  return ctr

#guard countPrimesNums 5 = 2
#guard countPrimesNums 10 = 4
#guard countPrimesNums 100 = 25
