import Batteries
open Std

def all_Characters_Same (s : String) : Bool :=
  let cs := s.data
  match cs with
  | [] => true
  | c :: rest =>
    let rec go (xs : List Char) : Bool :=
      match xs with
      | [] => true
      | d :: ds => if d == c then go ds else false
    go rest

#guard all_Characters_Same "python" == false
#guard all_Characters_Same "aaa" == true
#guard all_Characters_Same "data" == false
