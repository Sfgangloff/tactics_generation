import Batteries

open Std

def changeDateFormat (dt : String) : String :=
  let parts := dt.splitOn "-"
  match parts with
  | [y, m, d] => d ++ "-" ++ m ++ "-" ++ y
  | _ => dt

#guard changeDateFormat "2026-01-02" == "02-01-2026"
#guard changeDateFormat "2021-01-04" == "04-01-2021"
#guard changeDateFormat "2030-06-06" == "06-06-2030"
