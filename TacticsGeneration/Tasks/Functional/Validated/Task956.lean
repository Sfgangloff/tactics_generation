import Batteries

open Std

def isUpperASCII (c : Char) : Bool :=
  let n := c.toNat
  let a := ('A').toNat
  let z := ('Z').toNat
  n >= a && n <= z

def splitList (text : String) : List String :=
  let rec loop (cs : List Char) (bufRev : List Char) (accRev : List String) : List String :=
    match cs with
    | [] =>
      let accRev := if bufRev.isEmpty then accRev else (String.mk (bufRev.reverse)) :: accRev
      accRev.reverse
    | c :: cs' =>
      if isUpperASCII c then
        let accRev := if bufRev.isEmpty then accRev else (String.mk (bufRev.reverse)) :: accRev
        loop cs' [c] accRev
      else
        if bufRev.isEmpty then
          loop cs' [] accRev
        else
          loop cs' (c :: bufRev) accRev
  loop text.data [] []

#guard splitList "LearnToBuildAnythingWithGoogle" == ["Learn", "To", "Build", "Anything", "With", "Google"]
#guard splitList "ApmlifyingTheBlack+DeveloperCommunity" == ["Apmlifying", "The", "Black+", "Developer", "Community"]
#guard splitList "UpdateInTheGoEcoSystem" == ["Update", "In", "The", "Go", "Eco", "System"]
