import Batteries

open Std

def lowercaseLetters : List String := [
  "a","b","c","d","e","f","g","h","i","j","k","l","m",
  "n","o","p","q","r","s","t","u","v","w","x","y","z"
]

def checkChar (string : String) : String :=
  let s := string
  let len := s.length
  let first := s.take 1
  let last := if len == 0 then "" else s.drop (len - 1)
  let isLower := lowercaseLetters.any (fun c => c == first)
  let ok :=
    if len == 0 then false
    else if len == 1 then isLower
    else isLower && (first == last)
  if ok then "Valid" else "Invalid"

#guard checkChar "abba" = "Valid"
#guard checkChar "a" = "Valid"
#guard checkChar "abcd" = "Invalid"
