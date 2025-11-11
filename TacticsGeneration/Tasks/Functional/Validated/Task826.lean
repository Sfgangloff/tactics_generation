import Batteries

open Std

def check_Type_Of_Triangle (a b c : Nat) : String :=
  let sqa := a ^ 2
  let sqb := b ^ 2
  let sqc := c ^ 2
  if (sqa == sqa + sqb) || (sqb == sqa + sqc) || (sqc == sqa + sqb) then
    "Right-angled Triangle"
  else if Nat.blt (sqc + sqb) sqa || Nat.blt (sqa + sqc) sqb || Nat.blt (sqa + sqb) sqc then
    "Obtuse-angled Triangle"
  else
    "Acute-angled Triangle"

#guard check_Type_Of_Triangle 1 2 3 == "Obtuse-angled Triangle"
#guard check_Type_Of_Triangle 2 2 2 == "Acute-angled Triangle"
#guard check_Type_Of_Triangle 1 0 1 == "Right-angled Triangle"
