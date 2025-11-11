import Batteries

open Std

def natLe (a b : Nat) : Bool :=
  match Nat.decLe a b with
  | isTrue _ => true
  | isFalse _ => false

def charLe (a b : Char) : Bool := natLe a.toNat b.toNat

def isLowerAscii (c : Char) : Bool := charLe 'a' c && charLe c 'z'

def allLowerAscii (s : String) : Bool := (s.toList).all isLowerAscii

def text_lowercase_underscore (text : String) : String :=
  let parts := text.splitOn "_"
  if parts.length == 2 then
    let a := parts.getD 0 ""
    let b := parts.getD 1 ""
    if a != "" && b != "" && allLowerAscii a && allLowerAscii b then
      "Found a match!"
    else
      "Not matched!"
  else
    "Not matched!"

#guard text_lowercase_underscore "aab_cbbbc" = "Found a match!"
#guard text_lowercase_underscore "aab_Abbbc" = "Not matched!"
#guard text_lowercase_underscore "Aaab_abbbc" = "Not matched!"
#guard text_lowercase_underscore "aab-cbbbc" = "Not matched!"
