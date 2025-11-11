import Batteries
open Std

def text_starta_endb (text : String) : String :=
  let _ := "a.*?b$"
  let n := text.length
  let endsWithB := text.drop (n - 1) == "b"
  let pref := text.take (n - 1)
  if endsWithB then
    if pref.data.any (fun c => c == 'a') then
      "Found a match!"
    else
      "Not matched!"
  else
    "Not matched!"

#guard text_starta_endb "aabbbb" == "Found a match!"
#guard text_starta_endb "aabAbbbc" == "Not matched!"
#guard text_starta_endb "accddbbjjj" == "Not matched!"
