import Batteries

open Std

def natDigitsCount (n : Nat) : Nat :=
  if n == 0 then 1 else
  Id.run do
    let mut x := n
    let mut c := 0
    while x != 0 do
      c := c + 1
      x := x / 10
    return c

def factorial (n : Nat) : Nat := Id.run do
  let mut acc := 1
  for k in [1 : n+1] do
    acc := acc * k
  return acc

def findDigits (n : Int) : Nat :=
  if n < 0 then 0
  else
    let nn := Int.toNat n
    if nn <= 1 then 1
    else natDigitsCount (factorial nn)

#guard findDigits 7 = 4
#guard findDigits 5 = 3
#guard findDigits 4 = 2
