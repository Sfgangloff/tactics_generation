import Batteries
open Std

def listMax? (xs : List Nat) : Option Nat :=
  match xs with
  | [] => none
  | h :: t => some <| t.foldl (fun acc x => if x > acc then x else acc) h

def removeOne (xs : List Nat) (x : Nat) : List Nat :=
  match xs with
  | [] => []
  | h :: t => if h == x then t else h :: removeOne t x

def largeProduct (nums1 nums2 : List Nat) (N : Nat) : List Nat := Id.run do
  let prods := nums1.foldl (fun acc x => acc ++ nums2.map (fun y => x * y)) []
  let mut arr := prods
  let mut res : List Nat := []
  let mut i := 0
  while i < N do
    match listMax? arr with
    | none => break
    | some m =>
      res := res ++ [m]
      arr := removeOne arr m
      i := i + 1
  return res

#guard largeProduct [1, 2, 3, 4, 5, 6] [3, 6, 8, 9, 10, 6] 3 == [60, 54, 50]
#guard largeProduct [1, 2, 3, 4, 5, 6] [3, 6, 8, 9, 10, 6] 4 == [60, 54, 50, 48]
#guard largeProduct [1, 2, 3, 4, 5, 6] [3, 6, 8, 9, 10, 6] 5 == [60, 54, 50, 48, 45]
