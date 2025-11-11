import Batteries
open Std

def reverseVowels (str1 : String) : String :=
  let vowels := str1.foldl (init := []) fun vowels char =>
    if char ∈ "aeiouAEIOU".data then char :: vowels else vowels
  let vowelsList := vowels.reverse
  let rec process (s : List Char) (vowels : List Char) (acc : List Char) : List Char :=
    match s with
    | [] => acc.reverse
    | c :: cs =>
      if c ∈ "aeiouAEIOU".data then
        match vowels with
        | [] => process cs vowels (c :: acc)
        | v :: vs => process cs vs (v :: acc)
      else
        process cs vowels (c :: acc)
  String.mk <| process str1.data vowelsList []

#eval (reverseVowels "Python" == "Python")
#eval (reverseVowels "USA" == "ASU")
#eval (reverseVowels "ab" == "ba")
