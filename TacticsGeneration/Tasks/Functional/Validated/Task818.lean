import Batteries

open Std

def lowerCtr (str : String) : Nat := Id.run do
  let mut lower_ctr := 0
  for c in str.data do
    if c >= 'a' && c <= 'z' then
      lower_ctr := lower_ctr + 1
  return lower_ctr

#guard lowerCtr "abc" == 3
#guard lowerCtr "string" == 6
#guard lowerCtr "Python" == 5
