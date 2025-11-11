import Batteries
open Std

def tokenize (text : String) : List String :=
  (text.splitOn " ").filter (fun x => x ≠ "")

def better (a b : String × Nat × Nat) : Bool :=
  match a, b with
  | (_, ca, ia), (_, cb, ib) =>
    if ca > cb then true
    else if ca < cb then false
    else ia < ib

def pickBest (xs : List (String × Nat × Nat)) : Option (String × Nat × Nat) :=
  match xs with
  | [] => none
  | x :: xs' => some (xs'.foldl (fun best y => if better y best then y else best) x)

def removeByKey (xs : List (String × Nat × Nat)) (k : String) : List (String × Nat × Nat) :=
  match xs with
  | [] => []
  | (w,c,i) :: xs' => if w == k then xs' else (w,c,i) :: removeByKey xs' k

def findVal (m : Std.HashMap String Nat) (k : String) : Option Nat :=
  let rec go (ls : List (String × Nat)) : Option Nat :=
    match ls with
    | [] => none
    | (k', v) :: tl => if k' == k then some v else go tl
  go m.toList

def nCommonWords (text : String) (n : Nat) : List (String × Nat) := Id.run do
  let words := tokenize text
  let mut cnt : Std.HashMap String Nat := {}
  let mut first : Std.HashMap String Nat := {}
  let mut idx : Nat := 0
  for w in words do
    let c := (findVal cnt w).getD 0
    cnt := cnt.insert w (c + 1)
    if (findVal first w).isSome then
      ()
    else
      first := first.insert w idx
    idx := idx + 1
  let triples : List (String × Nat × Nat) :=
    cnt.toList.map (fun (kv : String × Nat) =>
      let w := kv.fst
      let c := kv.snd
      let i := (findVal first w).getD 0
      (w, c, i))
  let mut xs := triples
  let mut res : List (String × Nat) := []
  for _ in [: n] do
    match pickBest xs with
    | none => break
    | some (w,c,_) =>
      res := res ++ [(w, c)]
      xs := removeByKey xs w
  return res

#guard nCommonWords "python is a programming language" 1 == [("python", 1)]
#guard nCommonWords "python is a programming language" 1 == [("python", 1)]
#guard nCommonWords "python is a programming language" 5 == [("python", 1), ("is", 1), ("a", 1), ("programming", 1), ("language", 1)]
