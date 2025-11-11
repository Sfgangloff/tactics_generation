import Batteries

open Std

def count_charac (str1 : String) : Nat := Id.run do
  let mut total := 0
  for _ in str1.toList do
    total := total + 1
  return total

#guard count_charac "python programming" = 18
#guard count_charac "language" = 8
#guard count_charac "words" = 5
