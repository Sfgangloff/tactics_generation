import Batteries

open Std

def isAsciiDigit (c : Char) : Bool :=
  if ('0' ≤ c ∧ c ≤ '9') then true else false

def isAsciiLetter (c : Char) : Bool :=
  if (('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')) then true else false

def checkString (str : String) : Bool := Id.run do
  let mut flag_l := false
  let mut flag_n := false
  for c in str.data do
    if isAsciiLetter c then
      flag_l := true
    if isAsciiDigit c then
      flag_n := true
  return flag_l && flag_n

#guard checkString "thishasboth29" == true
#guard checkString "python" == false
#guard checkString "string" == false
