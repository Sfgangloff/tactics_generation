import Batteries

open Std

def extractValues (text : String) : List String :=
  let parts := text.splitOn "\""
  let rec go (ps : List String) (i : Nat) (acc : List String) : List String :=
    match ps with
    | [] => acc.reverse
    | p :: ps' =>
      let acc' := if i % 2 = 1 then p :: acc else acc
      go ps' (i+1) acc'
  go parts 0 []

#guard extractValues "\"Python\", \"PHP\", \"Java\"" = ["Python", "PHP", "Java"]
#guard extractValues "\"python\",\"program\",\"language\"" = ["python","program","language"]
#guard extractValues "\"red\",\"blue\",\"green\",\"yellow\"" = ["red","blue","green","yellow"]
