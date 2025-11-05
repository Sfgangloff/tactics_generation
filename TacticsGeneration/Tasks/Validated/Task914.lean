import Batteries

open Std

def checkPairs (cs : List Char) : Bool :=
  match cs with
  | a :: b :: c :: rest =>
      if a == c then
        checkPairs (b :: c :: rest)
      else
        false
  | _ => true

def is_Two_Alter (s : String) : Bool :=
  let cs := s.data
  if !checkPairs cs then
    false
  else
    match cs with
    | a :: b :: _ => if a == b then false else true
    | _ => false

#guard is_Two_Alter "abab" == true
#guard is_Two_Alter "aaaa" == false
#guard is_Two_Alter "xyz" == false
