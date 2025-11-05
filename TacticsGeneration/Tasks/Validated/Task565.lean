import Batteries
open Std

def split (word : String) : List String :=
  word.data.map (fun c => String.mk [c])

#guard split "python" == ["p","y","t","h","o","n"]
#guard split "Name" == ["N","a","m","e"]
#guard split "program" == ["p","r","o","g","r","a","m"]
