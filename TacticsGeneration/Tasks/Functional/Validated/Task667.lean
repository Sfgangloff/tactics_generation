import Batteries

open Std

def Check_Vow (string : String) (vowels : String) : Nat :=
  (string.data.filter (fun c => vowels.data.any (fun v => v == c))).length

#guard Check_Vow "corner" "AaEeIiOoUu" = 2
#guard Check_Vow "valid" "AaEeIiOoUu" = 2
#guard Check_Vow "true" "AaEeIiOoUu" = 2
