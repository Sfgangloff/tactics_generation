import Batteries

open Std

def occuranceSubstring (text pattern : String) : (String × Nat × Nat) := Id.run do
  let n := text.length
  let m := pattern.length
  let upto := if n >= m then n - m else 0
  for i in [0 : upto + 1] do
    if (text.drop i).take m == pattern then
      return ((text.drop i).take m, i, i + m)
  return ("", 0, 0)

#guard occuranceSubstring "python programming, python language" "python" = ("python", 0, 6)
#guard occuranceSubstring "python programming,programming language" "programming" = ("programming", 7, 18)
#guard occuranceSubstring "python programming,programming language" "language" = ("language", 31, 39)
