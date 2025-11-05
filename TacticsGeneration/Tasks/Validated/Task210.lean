import Batteries

open Std

private def allowedChars : List Char :=
  let lowers := (List.range 26).map (fun i => Char.ofNat ('a'.toNat + i))
  let uppers := (List.range 26).map (fun i => Char.ofNat ('A'.toNat + i))
  let digits := (List.range 10).map (fun i => Char.ofNat ('0'.toNat + i))
  lowers ++ uppers ++ digits ++ ['.']

private def allowedSet : HashSet Char := HashSet.ofList allowedChars

def isAllowedSpecificChar (s : String) : Bool :=
  s.data.all (fun c => allowedSet.contains c)

#guard isAllowedSpecificChar "ABCDEFabcdef123450" == true
#guard isAllowedSpecificChar "*&%@#!}{" == false
#guard isAllowedSpecificChar "HELLOhowareyou98765" == true
