import Batteries

open Std

def check (string : String) : String :=
  let p : HashSet Char := HashSet.ofList string.data
  let s01 : HashSet Char := HashSet.ofList ['0', '1']
  if p == s01 || p == HashSet.ofList ['0'] || p == HashSet.ofList ['1'] then
    "Yes"
  else
    "No"

#guard check "01010101010" = "Yes"
#guard check "name0" = "No"
#guard check "101" = "Yes"
