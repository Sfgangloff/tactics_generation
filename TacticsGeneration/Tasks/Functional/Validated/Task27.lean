import Batteries

open Std

def removeDigits (list : List String) : List String :=
  let pattern := "[0-9]"
  list.map (fun s => s.foldl (fun acc c => if c.isDigit then acc else acc.push c) "")

#guard removeDigits ["4words", "3letters", "4digits"] == ["words", "letters", "digits"]
#guard removeDigits ["28Jan", "12Jan", "11Jan"] == ["Jan", "Jan", "Jan"]
#guard removeDigits ["wonder1", "wonder2", "wonder3"] == ["wonder", "wonder", "wonder"]
