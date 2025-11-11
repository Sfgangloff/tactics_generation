import Batteries

open Std

def isAsciiLower (c : Char) : Bool :=
  if 'a' ≤ c then
    if c ≤ 'z' then true else false
  else
    false

def isAsciiUpper (c : Char) : Bool :=
  if 'A' ≤ c then
    if c ≤ 'Z' then true else false
  else
    false

def isDigit (c : Char) : Bool :=
  if '0' ≤ c then
    if c ≤ '9' then true else false
  else
    false

def isWordChar (c : Char) : Bool :=
  isAsciiLower c || isAsciiUpper c || isDigit c || c == '_'

def hasZMiddleAux : List Char → Bool
  | a :: b :: c :: t =>
      if (b == 'z') && isWordChar a && isWordChar c then
        true
      else
        hasZMiddleAux (b :: c :: t)
  | _ => false

def text_match_wordz_middle (text : String) : String :=
  if hasZMiddleAux text.data then "Found a match!" else "Not matched!"

#guard text_match_wordz_middle "pythonzabc." == "Found a match!"
#guard text_match_wordz_middle "xyzabc." == "Found a match!"
#guard text_match_wordz_middle "  lang  ." == "Not matched!"
