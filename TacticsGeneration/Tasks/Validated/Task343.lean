import Batteries

open Std

def digLet (s : String) : Nat × Nat :=
  let rec loop (cs : List Char) (d l : Nat) : Nat × Nat :=
    match cs with
    | [] => (l, d)
    | c :: cs' =>
      if c.isDigit then
        loop cs' (d+1) l
      else if c.isAlpha then
        loop cs' d (l+1)
      else
        loop cs' d l
  loop s.data 0 0

#guard digLet "python" = (6, 0)
#guard digLet "program" = (7, 0)
#guard digLet "python3.0" = (6, 2)
