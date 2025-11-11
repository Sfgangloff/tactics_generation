import Batteries
open Std

private def insertChar (x : Char) (xs : List Char) : List Char :=
  match xs with
  | [] => [x]
  | y :: ys =>
    if x < y then
      x :: y :: ys
    else
      y :: insertChar x ys

private def sortChars (xs : List Char) : List Char :=
  match xs with
  | [] => []
  | x :: xr => insertChar x (sortChars xr)

private def sortString (s : String) : String :=
  String.mk (sortChars s.data)

def isAnagram (a b : String) : Bool :=
  if a.length != b.length then
    false
  else
    sortString a == sortString b

def anagram_lambda (texts : List String) (str : String) : List String :=
  texts.filter (fun x => isAnagram str x)

#guard anagram_lambda ["bcda", "abce", "cbda", "cbea", "adcb"] "abcd" = ["bcda", "cbda", "adcb"]
#guard anagram_lambda ["recitals", " python"] "articles" = ["recitals"]
#guard anagram_lambda [" keep", " abcdef", " xyz"] " peek" = [" keep"]
