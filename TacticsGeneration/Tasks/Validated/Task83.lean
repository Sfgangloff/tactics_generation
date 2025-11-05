import Batteries

open Std

def getChar (str : String) : Char :=
  let sum := (str.toList.foldl (fun acc c => acc + (c.toNat - 'a'.toNat + 1)) 0)
  if sum % 26 == 0 then 'z'
  else Char.ofNat ((sum % 26) + 'a'.toNat - 1)

#guard getChar "abc" == 'f'
#guard getChar "gfg" == 't'
#guard getChar "ab" == 'c'
