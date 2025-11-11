import Batteries
open Std

def getItem (tup1 : List (Sum String Nat)) (index : Int) : Sum String Nat :=
  let len := tup1.length
  let n : Nat :=
    if index >= 0 then
      Int.toNat index
    else
      let k := Int.toNat (-index)
      len - k
  let rec getAt (xs : List (Sum String Nat)) (i : Nat) : Option (Sum String Nat) :=
    match xs, i with
    | [], _ => none
    | x :: _, 0 => some x
    | _ :: xs', i' + 1 => getAt xs' i'
  (getAt tup1 n).getD (Sum.inl "")

def t : List (Sum String Nat) := [Sum.inl "w", Sum.inr 3, Sum.inl "r", Sum.inl "e", Sum.inl "s", Sum.inl "o", Sum.inl "u", Sum.inl "r", Sum.inl "c", Sum.inl "e"]
#guard getItem t 3 = Sum.inl "e"
#guard getItem t (-4 : Int) = Sum.inl "u"
#guard getItem t (-3 : Int) = Sum.inl "r"
