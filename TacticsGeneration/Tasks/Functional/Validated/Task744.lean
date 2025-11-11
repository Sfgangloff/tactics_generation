import Batteries

open Std

def checkNone (testTup : List (Option Nat)) : Bool :=
  testTup.any (fun ele => match ele with | none => true | some _ => false)

#guard checkNone [some 10, some 4, some 5, some 6, none] == true
#guard checkNone [some 7, some 8, some 9, some 11, some 14] == false
#guard checkNone [some 1, some 2, some 3, some 4, none] == true
