import Batteries

open Std

def gcd (p q : Nat) : Nat := Id.run do
  let mut p := p
  let mut q := q
  while q != 0 do
    let oldP := p
    p := q
    q := oldP % p
  return p

def isCoprime (x y : Nat) : Bool := gcd x y == 1

#guard isCoprime 17 13 == true
#guard isCoprime 15 21 == false
#guard isCoprime 25 45 == false
