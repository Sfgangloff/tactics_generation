import Batteries

open Std

def matchNum (string : String) : Bool :=
  if string.take 1 == "5" then true else false

#guard matchNum "5-2345861" == true
#guard matchNum "6-2345861" == false
#guard matchNum "78910" == false
