import Batteries

open Std

def moveNum (test_str : String) : String :=
  let (res, dig) := (test_str.toList).foldl
    (fun (acc : String × String) (c : Char) =>
      let res := acc.fst
      let dig := acc.snd
      if c.isDigit then (res, dig.push c) else (res.push c, dig)
    ) ("", "")
  res ++ dig

#guard moveNum "I1love143you55three3000thousand" == "Iloveyouthreethousand1143553000"
#guard moveNum "Avengers124Assemble" == "AvengersAssemble124"
#guard moveNum "Its11our12path13to14see15things16do17things" == "Itsourpathtoseethingsdothings11121314151617"
