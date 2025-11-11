import Batteries
open Std

def isUndulating (n : String) : Bool :=
  if n.length ≤ 2 then
    false
  else
    let rec check (chars : List Char) (i : Nat) : Bool :=
      if i ≥ chars.length then true
      else
        match (chars.getD (i - 2) 'a'), (chars.getD i 'b') with
        | c1, c2 => if c1 != c2 then false else check chars (i + 1)
    check n.data 2

#guard isUndulating "1212121" == true
#guard isUndulating "1991" == false
#guard isUndulating "121" == true
