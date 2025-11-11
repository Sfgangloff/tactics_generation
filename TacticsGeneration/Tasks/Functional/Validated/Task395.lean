import Batteries
open Std

def firstNonRepeatingCharacter (str1 : String) : Option Char :=
  let cs := str1.data
  let rec pass1 (cs : List Char) (once : Std.HashSet Char) (multi : Std.HashSet Char) (orderRev : List Char) :
      Std.HashSet Char × Std.HashSet Char × List Char :=
    match cs with
    | [] => (once, multi, orderRev)
    | c :: cs' =>
      if multi.contains c then
        pass1 cs' once multi orderRev
      else if once.contains c then
        let once' := once.erase c
        let multi' := multi.insert c
        pass1 cs' once' multi' orderRev
      else
        let once' := once.insert c
        pass1 cs' once' multi (c :: orderRev)
  let (once, _, orderRev) := pass1 cs (Std.HashSet.empty) (Std.HashSet.empty) []
  let order := orderRev.reverse
  let rec findFirst (ord : List Char) : Option Char :=
    match ord with
    | [] => none
    | c :: cs' =>
      if once.contains c then some c else findFirst cs'
  findFirst order

#guard firstNonRepeatingCharacter "abcabc" = none
#guard firstNonRepeatingCharacter "abc" = some 'a'
#guard firstNonRepeatingCharacter "ababc" = some 'c'
