import Batteries

open Std

def colon_tuplex (tuplex : String × Nat × List Nat × Bool) (m n : Nat) : String × Nat × List Nat × Bool :=
  
  let (a, b, c, d) := tuplex
  if m == 2 then
    (a, b, c ++ [n], d)
  else
    tuplex

#guard colon_tuplex ("HELLO", 5, [], true) 2 50 == ("HELLO", 5, [50], true)
#guard colon_tuplex ("HELLO", 5, [], true) 2 100 == ("HELLO", 5, [100], true)
#guard colon_tuplex ("HELLO", 5, [], true) 2 500 == ("HELLO", 5, [500], true)
