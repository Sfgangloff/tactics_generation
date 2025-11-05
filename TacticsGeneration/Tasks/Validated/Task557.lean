import Batteries

open Std

def toggleString (string : String) : String :=
  let mapped := string.data.map (fun c =>
    if 'a' ≤ c && c ≤ 'z' then
      Char.ofNat (c.toNat - 'a'.toNat + 'A'.toNat)
    else if 'A' ≤ c && c ≤ 'Z' then
      Char.ofNat (c.toNat - 'A'.toNat + 'a'.toNat)
    else c
  )
  String.mk mapped

#guard toggleString "Python" == "pYTHON"
#guard toggleString "Pangram" == "pANGRAM"
#guard toggleString "LIttLE" == "liTTle"
