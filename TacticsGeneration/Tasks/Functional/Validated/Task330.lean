import Batteries
open Std

def findChar (text : String) : List String :=
  (text.splitOn " ").filter (fun w => let n := w.length; n >= 3 && n <= 5)

#guard findChar "For the four consumer complaints contact manager AKR reddy" == ["For", "the", "four", "AKR", "reddy"]
#guard findChar "Certain service are subject to change MSR" == ["are", "MSR"]
#guard findChar "Third party legal desclaimers" == ["Third", "party", "legal"]
