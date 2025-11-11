import Batteries

open Std

def joinWithSpace (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc y => acc ++ " " ++ y) x

def containsSubstring (s sub : String) : Bool := Id.run do
  if sub == "" then return true
  let n := s.length
  let m := sub.length
  if h : m > n then
    return false
  else
    let upper := n - m + 1
    for i in [0 : upper] do
      if (s.drop i).take m == sub then
        return true
    return false

def removeWords (list1 : List String) (charlist : List String) : List String :=
  list1.map (fun line =>
    let words := line.splitOn " "
    let filtered := words.filter (fun word => not (charlist.any (fun phrase => containsSubstring word phrase)))
    joinWithSpace filtered
  )

#guard removeWords ["Red color", "Orange#", "Green", "Orange @", "White"] ["#", "color", "@"] == ["Red", "", "Green", "Orange", "White"]
#guard removeWords ["Red &", "Orange+", "Green", "Orange @", "White"] ["&", "+", "@"] == ["Red", "", "Green", "Orange", "White"]
#guard removeWords ["Red &", "Orange+", "Green", "Orange @", "White"] ["@"] == ["Red &", "Orange+", "Green", "Orange", "White"]
