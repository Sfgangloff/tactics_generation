import Batteries

open Std

def isLowerPython (cs : List Char) : Bool :=
  let rec go (cs : List Char) (seen : Bool) : Bool :=
    match cs with
    | [] => seen
    | c :: t =>
      if c.isAlpha then
        if c.isLower then go t true else false
      else
        go t seen
  go cs false

def firstUpper (s : String) : Bool :=
  match s.data with
  | [] => false
  | c :: _ => c.isUpper

def restLower (s : String) : Bool :=
  match s.data with
  | [] => false
  | _ :: t => isLowerPython t

def sampleNam (sampleNames : List String) : Nat :=
  let filtered := sampleNames.filter (fun el => firstUpper el && restLower el)
  let joined := filtered.foldl (fun acc s => acc ++ s) ""
  joined.length

#guard sampleNam ["sally", "Dylan", "rebecca", "Diana", "Joanne", "keith"] = 16
#guard sampleNam ["php", "res", "Python", "abcd", "Java", "aaa"] = 10
#guard sampleNam ["abcd", "Python", "abba", "aba"] = 6
