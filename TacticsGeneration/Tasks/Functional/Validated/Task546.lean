import Batteries

open Std

def lastOccurenceChar (string : String) (char : Char) : Option Nat := Id.run do
  let mut flag : Option Nat := none
  let n := string.length
  let target := String.singleton char
  for i in [0 : n] do
    if (string.drop i).take 1 == target then
      flag := some i
  match flag with
  | none => return none
  | some i => return some (i + 1)

#guard lastOccurenceChar "hello world" 'l' == some 10
#guard lastOccurenceChar "language" 'g' == some 7
#guard lastOccurenceChar "little" 'y' == none
