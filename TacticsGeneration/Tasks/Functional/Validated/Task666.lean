import Batteries

open Std

def countChar (string : String) (char : Char) : Nat := Id.run do
  let mut count := 0
  for c in string.toList do
    if c == char then
      count := count + 1
  return count

#guard countChar "Python" 'o' = 1
#guard countChar "little" 't' = 2
#guard countChar "assert" 's' = 2
