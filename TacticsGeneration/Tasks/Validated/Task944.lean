import Batteries

open Std

def numPosition (text : String) : Nat :=
  let rec loop (cs : List Char) (i : Nat) : Nat :=
    match cs with
    | [] => 0  
    | c :: cs' => if c.isDigit then i else loop cs' (i+1)
  loop text.toList 0

#guard numPosition "there are 70 flats in this apartment" = 10
#guard numPosition "every adult have 32 teeth" = 17
#guard numPosition "isha has 79 chocolates in her bag" = 9
