import Batteries

open Std

def splitWords (s : String) : List String :=
  let rec loop (cs : List Char) (curr : List Char) (acc : List (List Char)) : List (List Char) :=
    match cs with
    | [] => if curr.isEmpty then acc else (curr.reverse :: acc)
    | c :: cs' =>
      if c = ' ' then
        if curr.isEmpty then loop cs' [] acc
        else loop cs' [] (curr.reverse :: acc)
      else
        loop cs' (c :: curr) acc
  let wordsRev := loop s.data [] []
  let words := wordsRev.reverse
  words.map (fun chars => String.mk chars)

def joinWithSpace (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: xs => xs.foldl (fun acc s => acc ++ " " ++ s) x

def removeLength (test_str : String) (K : Nat) : String :=
  let temp := splitWords test_str
  let res := temp.filter (fun ele => ele.length != K)
  joinWithSpace res

#guard removeLength "The person is most value tet" 3 == "person is most value"
#guard removeLength "If you told me about this ok" 4 == "If you me about ok"
#guard removeLength "Forces of darkeness is come into the play" 4 == "Forces of darkeness is the"
