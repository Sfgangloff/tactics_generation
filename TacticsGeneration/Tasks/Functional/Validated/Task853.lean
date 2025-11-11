import Batteries

open Std

def sumOfOddFactors (n : Nat) : Nat := Id.run do
  
  let mut m := n
  let mut res := 1
  while m % 2 == 0 do
    m := m / 2
  let ub := Nat.sqrt m + 1
  for i in [3 : ub] do
    let mut count := 0
    let mut curr_sum := 1
    let mut curr_term := 1
    while m % i == 0 do
      count := count + 1
      m := m / i
      curr_term := curr_term * i
      curr_sum := curr_sum + curr_term
    res := res * curr_sum
  if m >= 2 then
    res := res * (1 + m)
  return res

#guard sumOfOddFactors 30 = 24
#guard sumOfOddFactors 18 = 13
#guard sumOfOddFactors 2 = 1
