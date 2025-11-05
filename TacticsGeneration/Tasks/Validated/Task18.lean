import Batteries
open Std

def NO_OF_CHARS : Nat := 256

def strToList (s : String) : List Char := s.toList

def lstToString (L : List Char) : String := String.mk L

def getCharCountArray (s : String) : Array Nat := Id.run do
  let mut count := Array.replicate NO_OF_CHARS 0
  for c in s.toList do
    let idx := c.toNat
    
    count := count.set! idx (count[idx]! + 1)
  return count

def removeDirtyChars (string second_string : String) : String := Id.run do
  let count := getCharCountArray second_string
  let mut res_ind := 0
  let mut str_list := (strToList string).toArray
  for ip_ind in [0 : str_list.size] do
    let c := str_list[ip_ind]!
    let idx := c.toNat
    if count[idx]! == 0 then
      str_list := str_list.set! res_ind c
      res_ind := res_ind + 1
    else
      pure ()
  return lstToString ((str_list.extract 0 res_ind).toList)

#guard removeDirtyChars "probasscurve" "pros" = "bacuve"
#guard removeDirtyChars "digitalindia" "talent" = "digiidi"
#guard removeDirtyChars "exoticmiles" "toxic" = "emles"
