import Batteries

open Std

def findMinSum (num : Nat) : Nat := Id.run do
  let mut s : Nat := 0
  let mut i : Nat := 2
  let mut n : Nat := num
  while i * i <= n do
    while n % i == 0 do
      s := s + i
      n := n / i
    i := i + 1
  s := s + n
  return s

#guard findMinSum 12 = 7
#guard findMinSum 105 = 15
#guard findMinSum 2 = 2
