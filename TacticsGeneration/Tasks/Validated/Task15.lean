import Batteries
open Std

def splitLowerString (text : String) : List String :=
  let rec aux (current : String) (remaining : List Char) (acc : List String) : List String :=
    match remaining with
    | [] => if current.isEmpty then acc else acc ++ [current]
    | c::cs =>
      if c.isLower then
        if current.isEmpty then
          aux (String.mk [c]) cs acc
        else
          aux (String.mk [c]) cs (acc ++ [current])
      else
        aux (current.push c) cs acc
  aux "" text.data []

#eval splitLowerString "AbCd" == ["bC", "d"]
#eval splitLowerString "Python" == ["y", "t", "h", "o", "n"]
#eval splitLowerString "Programming" == ["r", "o", "g", "r", "a", "m", "m", "i", "n", "g"]
