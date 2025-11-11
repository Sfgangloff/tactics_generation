import Batteries

open Std

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def extractMax (input : String) : Nat := Id.run do
  let mut maxVal : Nat := 0
  let mut curr : Nat := 0
  let mut inNum : Bool := false
  let mut found : Bool := false
  for c in input.data do
    if isDigit c then
      curr := curr * 10 + (c.toNat - '0'.toNat)
      inNum := true
    else
      if inNum then
        if found then
          maxVal := max maxVal curr
        else
          maxVal := curr
          found := true
        inNum := false
        curr := 0
  if inNum then
    if found then
      maxVal := max maxVal curr
    else
      maxVal := curr
      found := true
  return maxVal

#guard extractMax "100klh564abc365bg" = 564
#guard extractMax "hello300how546mer231" = 546
#guard extractMax "its233beenalong343journey234" = 343
