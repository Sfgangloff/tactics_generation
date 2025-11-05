import Batteries
open Std

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

def allLower (s : String) : Bool :=
  s.data.all isLower

def getCharAt (s : String) (i : Nat) : Option Char :=
  let rec go (l : List Char) (i : Nat) : Option Char :=
    match l, i with
    | [], _ => none
    | c :: _, 0 => some c
    | _ :: t, i+1 => go t i
  go s.data i

def matchRe (text : String) : String := Id.run do
  let n := text.length
  
  
  for j in [1 : n] do
    let suffix := text.drop j
    match getCharAt text (j - 1) with
    | some c =>
      if isUpper c && allLower suffix then
        return "Yes"
    | none => pure ()
  return "No"

#guard matchRe "Geeks" == "Yes"
#guard matchRe "geeksforGeeks" == "Yes"
#guard matchRe "geeks" == "No"
