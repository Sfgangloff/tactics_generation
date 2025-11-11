import Batteries

open Std

def isLowercaseLetters (s : String) : Bool :=
  match s.data with
  | [] => false
  | cs => cs.all (fun c => c >= 'a' && c <= 'z')

def textMatch (text : String) : String :=
  match text.splitOn "_" with
  | [a, b] =>
    if isLowercaseLetters a && isLowercaseLetters b then
      "Found a match!"
    else
      "Not matched!"
  | _ => "Not matched!"

#guard textMatch "aab_cbbbc" = "Found a match!"
#guard textMatch "aab_Abbbc" = "Not matched!"
#guard textMatch "Aaab_abbbc" = "Not matched!"
#guard textMatch "aab-cbbbc" = "Not matched!"
