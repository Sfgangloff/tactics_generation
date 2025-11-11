import Batteries

open Std

def number_ctr (str : String) : Nat := Id.run do
  let mut number_ctr := 0
  for c in str.data do
    if c >= '0' && c <= '9' then
      number_ctr := number_ctr + 1
  return number_ctr

#guard number_ctr "program2bedone" = 1
#guard number_ctr "3wonders" = 1
#guard number_ctr "123" = 3
