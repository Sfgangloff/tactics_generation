import Batteries

open Std

def rev (num : Nat) : Nat := Id.run do
  let mut n := num
  let mut revNum := 0
  while n > 0 do
    revNum := revNum * 10 + n % 10
    n := n / 10
  return revNum

def check (n : Nat) : Bool :=
  2 * rev n == n + 1

#guard check 70 == false
#guard check 23 == false
#guard check 73 == true
