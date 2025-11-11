import Batteries

open Std

def upperCtr (str : String) : Nat := Id.run do
  let mut upper_ctr := 0
  let chars := str.toList
  for i in [0 : chars.length] do
    let ch := chars.getD i ' '
    if ch >= 'A' && ch <= 'Z' then
      upper_ctr := upper_ctr + 1
    return upper_ctr
  return upper_ctr

#guard upperCtr "PYthon" = 1
#guard upperCtr "BigData" = 1
#guard upperCtr "program" = 0
