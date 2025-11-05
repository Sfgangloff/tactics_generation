import Batteries

open Std

def findLiterals (text : String) (pattern : String) : (String × Nat × Nat) := Id.run do
  let n := text.length
  let m := pattern.length
  if m == 0 then
    return (pattern, 0, 0)
  if m > n then
    return (pattern, n, n)
  for i in [: (n - m + 1)] do
    if (text.drop i).take m == pattern then
      return (pattern, i, i + m)
  
  return (pattern, n, n)

#guard findLiterals "The quick brown fox jumps over the lazy dog." "fox" = ("fox", 16, 19)
#guard findLiterals "Its been a very crazy procedure right" "crazy" = ("crazy", 16, 21)
#guard findLiterals "Hardest choices required strongest will" "will" = ("will", 35, 39)
