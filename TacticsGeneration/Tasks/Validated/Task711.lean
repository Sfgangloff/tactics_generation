import Batteries

open Std

def productEqual (n : Nat) : Bool := Id.run do
  if n < 10 then return false
  let mut m := n
  let mut prodOdd := 1
  let mut prodEven := 1
  while m > 0 do
    let digit := m % 10
    prodOdd := prodOdd * digit
    m := m / 10
    if m == 0 then break
    let digit2 := m % 10
    prodEven := prodEven * digit2
    m := m / 10
  return prodOdd == prodEven

#guard productEqual 2841 == true
#guard productEqual 1234 == false
#guard productEqual 1212 == false
