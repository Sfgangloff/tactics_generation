import Batteries

open Std

def romVal (c : Char) : Nat :=
  match c with
  | 'I' => 1
  | 'V' => 5
  | 'X' => 10
  | 'L' => 50
  | 'C' => 100
  | 'D' => 500
  | 'M' => 1000
  | _ => 0

def roman_to_int (s : String) : Nat := Id.run do
  let chars := s.toList
  let mut intVal : Nat := 0
  let mut prevVal : Nat := 0
  for c in chars do
    let curr := romVal c
    if prevVal > 0 && curr > prevVal then
      intVal := intVal + (curr - 2 * prevVal)
    else
      intVal := intVal + curr
    prevVal := curr
  return intVal

#guard roman_to_int "MMMCMLXXXVI" == 3986
#guard roman_to_int "MMMM" == 4000
#guard roman_to_int "C" == 100
