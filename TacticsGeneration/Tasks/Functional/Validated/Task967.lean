import Batteries

open Std

def check (string : String) : String :=
  let vowels := "AEIOUaeiou".toList
  let found := string.toList.foldl (fun acc c =>
    if (vowels.any (fun v => v == c)) && !(acc.any (fun v => v == c)) then
      c :: acc
    else acc
  ) []
  if found.length >= 5 then "accepted" else "not accepted"

#guard check "SEEquoiaL" == "accepted"
#guard check "program" == "not accepted"
#guard check "fine" == "not accepted"
