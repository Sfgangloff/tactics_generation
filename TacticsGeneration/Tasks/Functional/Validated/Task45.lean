import Batteries
open Std

def findGcd (x y : Nat) : Nat := Id.run do
  let mut a := x
  let mut b := y
  while b != 0 do
    let tmp := b
    b := a % b
    a := tmp
  return a

def getGcd (l : List Nat) : Nat := Id.run do
  let mut gcd := findGcd (l.getD 0 0) (l.getD 1 0)  
  for i in [2 : l.length] do
    gcd := findGcd gcd (l.getD i 0)  
  return gcd

#guard getGcd [2, 4, 6, 8, 16] = 2
#guard getGcd [1, 2, 3] = 1
#guard getGcd [2, 4, 6, 8] = 2
