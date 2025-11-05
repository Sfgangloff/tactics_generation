import Batteries

open Std

def isSublist (l s : List Nat) : Bool :=
  if s == [] then
    true
  else if s == l then
    true
  else if s.length > l.length then
    false
  else Id.run do
    let mut subSet := false
    for i in [0 : l.length] do
      if l.getD i 0 == s.getD 0 0 then
        let mut n := 1
        while (n < s.length) && (l.getD (i+n) 0 == s.getD n 0) do
          n := n + 1
        if n == s.length then
          subSet := true
    return subSet

#guard isSublist [2,4,3,5,7] [3,7] == false
#guard isSublist [2,4,3,5,7] [4,3] == true
#guard isSublist [2,4,3,5,7] [1,6] == false
