import Batteries
open Std

def checkInteger (text : String) : Option Bool :=
  let text := text.trim
  if text.length < 1 then
    none
  else
    let allDigits (s : String) (start : Nat) : Bool :=
      s.drop start |>.all (fun ch => ch.isDigit)
    let firstCharIsSign :=
      match text.data with
      | [] => false
      | c::_ => c == '+' || c == '-'
    if allDigits text 0 then
      some true
    else if firstCharIsSign && allDigits text 1 then
      some true
    else
      some false

#eval checkInteger "python" == some false
#eval checkInteger "1" == some true
#eval checkInteger "12345" == some true
