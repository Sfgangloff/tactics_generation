import Batteries

open Std

def sumOfPrimes (n : Nat) : Nat := Id.run do
  let mut prime : Array Bool := Array.replicate (n + 1) true
  let mut p := 2
  while p * p <= n do
    if prime[p]! then
      let mut i := p * 2
      while i <= n do
        prime := prime.set! i false
        i := i + p
    p := p + 1
  let mut s := 0
  let mut i := 2
  while i <= n do
    if prime[i]! then
      s := s + i
    i := i + 1
  return s

#guard sumOfPrimes 10 = 17
#guard sumOfPrimes 20 = 77
#guard sumOfPrimes 5 = 10
