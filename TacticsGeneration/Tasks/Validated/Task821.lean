import Batteries
open Std

def mergeDictionaries (dict1 dict2 : List (String × String)) : HashMap String String := Id.run do
  let mut m : HashMap String String := {}
  
  for (k, v) in dict2 do
    m := m.insert k v
  for (k, v) in dict1 do
    m := m.insert k v
  return m

def lookupKey (m : HashMap String String) (k : String) : Option String :=
  m.fold (fun acc k' v' =>
    match acc with
    | some _ => acc
    | none => if k' == k then some v' else none
  ) (none : Option String)

def allPairsMatch (m : HashMap String String) (xs : List (String × String)) : Bool :=
  let rec loop (ys : List (String × String)) : Bool :=
    match ys with
    | [] => true
    | (k, v) :: t =>
      match lookupKey m k with
      | some v' => if v' == v then loop t else false
      | none => false
  loop xs

#guard
  let got := mergeDictionaries [("R", "Red"), ("B", "Black"), ("P", "Pink")] [("G", "Green"), ("W", "White")]
  let expected := [("B", "Black"), ("R", "Red"), ("P", "Pink"), ("G", "Green"), ("W", "White")]
  allPairsMatch got expected && got.size == expected.length

#guard
  let got := mergeDictionaries [("R", "Red"), ("B", "Black"), ("P", "Pink")] [("O", "Orange"), ("W", "White"), ("B", "Black")]
  let expected := [("O", "Orange"), ("P", "Pink"), ("B", "Black"), ("W", "White"), ("R", "Red")]
  allPairsMatch got expected && got.size == expected.length

#guard
  let got := mergeDictionaries [("G", "Green"), ("W", "White")] [("O", "Orange"), ("W", "White"), ("B", "Black")]
  let expected := [("W", "White"), ("O", "Orange"), ("G", "Green"), ("B", "Black")]
  allPairsMatch got expected && got.size == expected.length
