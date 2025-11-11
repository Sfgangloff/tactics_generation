import Batteries

open Std

def removeAllSpaces (text : String) : String :=
  String.mk (text.data.filter (fun c => !c.isWhitespace))

#guard removeAllSpaces "python  program" == "pythonprogram"
#guard removeAllSpaces "python   programming    language" == "pythonprogramminglanguage"
#guard removeAllSpaces "python                     program" == "pythonprogram"
