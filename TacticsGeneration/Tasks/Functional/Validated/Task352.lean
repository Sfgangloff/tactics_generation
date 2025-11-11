import Batteries
open Std

private def listNth? {α} : List α → Nat → Option α
| [], _ => none
| x :: _, 0 => some x
| _ :: xs, n+1 => listNth? xs n

def unique_Characters (str : String) : Bool := Id.run do
  let chars := str.data
  let n := chars.length
  for i in [0 : n] do
    for j in [i+1 : n] do
      match listNth? chars i, listNth? chars j with
      | some c1, some c2 =>
        if c1 == c2 then
          return false
      | _, _ => pure ()
  return true

#guard unique_Characters "aba" == false
#guard unique_Characters "abc" == true
#guard unique_Characters "abab" == false
