import Batteries

open Std

def joinSep (l : List String) (sep : String) : String :=
  match l with
  | [] => ""
  | s :: ss => ss.foldl (fun acc x => acc ++ sep ++ x) s

def allNone : List (Option Nat) → Bool
  | [] => true
  | none :: xs => allNone xs
  | some _ :: _ => false

def reprElem : Option Nat → String
  | none => "None"
  | some n => toString n

def reprTuple (xs : List (Option Nat)) : String :=
  match xs with
  | [a] => "(" ++ reprElem a ++ ",)"
  | _ => "(" ++ joinSep (xs.map reprElem) ", " ++ ")"

def reprListTuples (xss : List (List (Option Nat))) : String :=
  "[" ++ joinSep (xss.map reprTuple) ", " ++ "]"

def removeTuple (test_list : List (List (Option Nat))) : String :=
  let res := test_list.filter (fun sub => !(allNone sub))
  reprListTuples res

#guard removeTuple [[none, some 2], [none, none], [some 3, some 4], [some 12, some 3], [none]] = "[(None, 2), (3, 4), (12, 3)]"
#guard removeTuple [[none, none], [none, none], [some 3, some 6], [some 17, some 3], [none, some 1]] = "[(3, 6), (17, 3), (None, 1)]"
#guard removeTuple [[some 1, some 2], [some 2, none], [some 3, none], [some 24, some 3], [none, none]] = "[(1, 2), (2, None), (3, None), (24, 3)]"
