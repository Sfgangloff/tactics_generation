import Batteries

open Std

def isUpperASCII (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isLowerASCII (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

def countPrefix {α} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if p x then 1 + countPrefix p xs else 0

def textUppercaseLowercase (text : String) : String :=
  let rev := text.data.reverse
  let lowerCount := countPrefix isLowerASCII rev
  if lowerCount = 0 then
    "Not matched!"
  else
    let rest := rev.drop lowerCount
    let upperCount := countPrefix isUpperASCII rest
    if upperCount = 0 then "Not matched!" else "Found a match!"

#guard textUppercaseLowercase "AaBbGg" == "Found a match!"
#guard textUppercaseLowercase "aA" == "Not matched!"
#guard textUppercaseLowercase "PYTHON" == "Not matched!"
