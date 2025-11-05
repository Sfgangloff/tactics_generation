import Batteries

open Std

def replaceSpaces (text : String) : String :=
  let chars := text.data.map (fun c => if c == ' ' then '_' else c)
  String.mk chars

#guard replaceSpaces "Jumanji The Jungle" = "Jumanji_The_Jungle"
#guard replaceSpaces "The Avengers" = "The_Avengers"
#guard replaceSpaces "Fast and Furious" = "Fast_and_Furious"
