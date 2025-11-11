import Batteries

open Std

def isAsciiAlphaNum (c : Char) : Bool :=
  let n := c.toNat
  ((n >= 'a'.toNat && n <= 'z'.toNat) ||
   (n >= 'A'.toNat && n <= 'Z'.toNat) ||
   (n >= '0'.toNat && n <= '9'.toNat))

def checkAlphanumeric (string : String) : String :=
  let lastStr := string.drop (string.length - 1)
  match lastStr.toList.head? with
  | some c => if isAsciiAlphaNum c then "Accept" else "Discard"
  | none => "Discard"

#guard checkAlphanumeric "dawood@" = "Discard"
#guard checkAlphanumeric "skdmsam326" = "Accept"
#guard checkAlphanumeric "cooltricks@" = "Discard"
