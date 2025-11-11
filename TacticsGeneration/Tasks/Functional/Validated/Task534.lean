import Batteries

open Std

def searchLiteral (pattern : String) (text : String) : Nat × Nat := Id.run do
  let n := text.length
  let m := pattern.length
  for i in [0 : (n + 1) - m] do
    if (text.drop i).take m == pattern then
      return (i, i + m)
  return (0, 0)

#guard searchLiteral "python" "python programming language" = (0, 6)
#guard searchLiteral "programming" "python programming language" = (7, 18)
#guard searchLiteral "language" "python programming language" = (19, 27)
