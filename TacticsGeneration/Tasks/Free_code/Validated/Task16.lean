import Batteries



/-!
  Auto-generated from task 16.
  Module: Task16
-/

open Std

namespace Task16

-- Check if a string is a non-empty sequence of lowercase letters a..z
def isLowercaseLetters (s : String) : Bool :=
  match s.data with
  | [] => false
  | cs => allLower cs
where
  allLower (cs : List Char) : Bool :=
    match cs with
    | [] => true
    | c :: cs' => if 'a' ≤ c && c ≤ 'z' then allLower cs' else false

-- Returns "Found a match!" if the whole string is two lowercase sequences joined by a single underscore
def textLowercaseUnderscore (s : String) : String :=
  match s.splitOn "_" with
  | [a, b] => if isLowercaseLetters a && isLowercaseLetters b then "Found a match!" else "Not matched!"
  | _ => "Not matched!"

end Task16


-- Tests
open Task16

#guard textLowercaseUnderscore "aab_cbbbc" = "Found a match!"
#guard textLowercaseUnderscore "aab_Abbbc" = "Not matched!"
#guard textLowercaseUnderscore "Aaab_abbbc" = "Not matched!"
#guard textLowercaseUnderscore "aab-cbbbc" = "Not matched!"
