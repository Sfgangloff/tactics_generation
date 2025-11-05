import Batteries

open Std

def insertBy {α} (le : α → α → Bool) (x : α) : List α → List α
| [] => [x]
| y :: ys => if le x y then x :: y :: ys else y :: insertBy le x ys

def isort {α} (le : α → α → Bool) : List α → List α
| [] => []
| y :: ys => insertBy le y (isort le ys)

def charLE (a b : Char) : Bool := Nat.ble a.toNat b.toNat

def joinWith (sep : String) (cs : List Char) : String :=
  match cs with
  | [] => ""
  | c :: cs =>
    cs.foldl (fun acc ch => acc ++ sep ++ String.singleton ch) (String.singleton c)

def checkPermutation (str1 str2 : String) : Bool :=
  let n1 := str1.length
  let n2 := str2.length
  if n1 != n2 then
    false
  else
    let a := isort charLE str1.data
    let b := isort charLE str2.data
    let s1 := joinWith " " a
    let s2 := joinWith " " b
    s1.take n1 == s2.take n2

#guard checkPermutation "abc" "cba" == true
#guard checkPermutation "test" "ttew" == false
#guard checkPermutation "xxyz" "yxzx" == true
