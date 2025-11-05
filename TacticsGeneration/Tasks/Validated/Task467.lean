import Batteries

open Std

def decimal_to_Octal (deciNum : Nat) : Nat := Id.run do
  let mut octalNum := 0
  let mut countval := 1
  let mut deciNum := deciNum
  let _dNo := deciNum
  while deciNum != 0 do
    let remainder := deciNum % 8
    octalNum := octalNum + remainder * countval
    countval := countval * 10
    deciNum := deciNum / 8
  return octalNum

#guard decimal_to_Octal 10 == 12
#guard decimal_to_Octal 2 == 2
#guard decimal_to_Octal 33 == 41
