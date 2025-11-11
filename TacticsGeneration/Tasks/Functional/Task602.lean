import Batteries
open Std

def countIn (l : List Char) (c : Char) : Nat :=
  l.foldl (fun acc d => if d = c then acc + 1 else acc) 0

def firstRepeatedChar_loop (prefix : List Char) (rest : List Char) : String :=
  match rest with
  | [] => "None"
  | c :: cs =>
    let prefix2 := prefix ++ [c];
    if countIn prefix2 c > 1 then String.mk [c] else firstRepeatedChar_loop prefix2 cs

def firstRepeatedChar (str1 : String) : String :=
  firstRepeatedChar_loop [] str1.data

#guard firstRepeatedChar "abcabc" = "a"
#guard firstRepeatedChar "abc" = "None"
#guard firstRepeatedChar "123123" = "1"
