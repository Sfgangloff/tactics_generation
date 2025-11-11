import Batteries

open Std

def changeDateFormat (dt : String) : String :=
  match dt.splitOn "-" with
  | [y, m, d] => d ++ "-" ++ m ++ "-" ++ y
  | _ => dt

#guard changeDateFormat "2026-01-02" = "02-01-2026"
#guard changeDateFormat "2020-11-13" = "13-11-2020"
#guard changeDateFormat "2021-04-26" = "26-04-2021"
