import Batteries

open Std

def removeSpaces (text : String) : String :=
  let (_, acc) := text.foldl (fun (st : Bool × List Char) (c : Char) =>
    let (prevSpace, acc) := st
    if c == ' ' then
      if prevSpace then (true, acc) else (true, ' ' :: acc)
    else
      (false, c :: acc)) (false, [])
  String.mk acc.reverse

#guard removeSpaces "python  program" = "python program"
#guard removeSpaces "python   programming    language" = "python programming language"
#guard removeSpaces "python                     program" = "python program"
