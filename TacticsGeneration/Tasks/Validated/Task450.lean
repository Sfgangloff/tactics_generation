import Batteries

open Std

def extract_string (str : List String) (l : Nat) : List String :=
  str.filter (fun e => e.length == l)

#guard extract_string ["Python", "list", "exercises", "practice", "solution"] 8 == ["practice", "solution"]
#guard extract_string ["Python", "list", "exercises", "practice", "solution"] 6 == ["Python"]
#guard extract_string ["Python", "list", "exercises", "practice", "solution"] 9 == ["exercises"]
