import Batteries
open Std

def insertBy {α} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def isort {α} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy le x (isort le xs)

def lexLe : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    if x < y then true
    else if y < x then false
    else lexLe xs ys

def buildIndexMap (s : String) : HashMap Char (List Nat) := Id.run do
  let mut m : HashMap Char (List Nat) := {}
  let mut i : Nat := 0
  for c in s.data do
    let old := (m.get? c).getD []
    m := m.insert c (old ++ [i])
    i := i + 1
  return m

def collectValues (m : HashMap Char (List Nat)) : List (List Nat) :=
  m.fold (fun acc _ v => v :: acc) []

def is_Isomorphic (str1 str2 : String) : Bool :=
  let dictStr1 := buildIndexMap str1
  let dictStr2 := buildIndexMap str2
  let vals1 := collectValues dictStr1
  let vals2 := collectValues dictStr2
  let s1 := isort lexLe vals1
  let s2 := isort lexLe vals2
  s1 == s2

#guard is_Isomorphic "paper" "title" == true
#guard is_Isomorphic "ab" "ba" == true
#guard is_Isomorphic "ab" "aa" == false
