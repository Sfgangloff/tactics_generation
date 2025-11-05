import Batteries

open Std

private def minOfList (h : Char) (t : List Char) : Char :=
  t.foldl (fun m y => if y ≤ m then y else m) h

private def removeFirst (xs : List Char) (c : Char) : List Char :=
  match xs with
  | [] => []
  | x :: xs' => if x == c then xs' else x :: removeFirst xs' c

private def takeMin (xs : List Char) : Option (Char × List Char) :=
  match xs with
  | [] => none
  | h :: t =>
    let m := minOfList h t
    let rest := removeFirst (h :: t) m
    some (m, rest)

private def selectionSort (xs : List Char) : List Char :=
  let rec loop (k : Nat) (ys : List Char) (acc : List Char) : List Char :=
    match k with
    | 0 => acc.reverse
    | Nat.succ k' =>
      match takeMin ys with
      | none => acc.reverse
      | some (m, ys') => loop k' ys' (m :: acc)
  loop xs.length xs []

def sort_String (str : String) : String :=
  String.mk (selectionSort str.data)

#guard sort_String "cba" = "abc"
#guard sort_String "data" = "aadt"
#guard sort_String "zxy" = "xyz"
