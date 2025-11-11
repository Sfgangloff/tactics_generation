import Batteries

open Std

def countDigits (num1 num2 : Nat) : Nat := Id.run do
  let mut number := num1 + num2
  let mut count := 0
  while number != 0 do
    number := number / 10
    count := count + 1
  return count

#guard countDigits 9875 10 = 4
#guard countDigits 98759853034 100 = 11
#guard countDigits 1234567 500 = 7
