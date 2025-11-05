import Batteries

open Std

def check_Equality (s : String) : Bool :=
  let n := s.length
  if n = 0 then
    false
  else
    let first := s.take 1
    let last := s.drop (n - 1)
    first == last

def count_Substring_With_Equal_Ends (s : String) : Nat := Id.run do
  let n := s.length
  let mut result := 0
  for i in [0 : n] do
    for j in [1 : n - i + 1] do
      let sub := (s.drop i).take j
      if check_Equality sub then
        result := result + 1
  return result

#guard count_Substring_With_Equal_Ends "aba" == 4
#guard count_Substring_With_Equal_Ends "abcab" == 7
#guard count_Substring_With_Equal_Ends "abc" == 3
