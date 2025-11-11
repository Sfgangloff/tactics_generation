import Batteries

open Std

def cmpNat (a b : Nat) : Ordering :=
  if a == b then Ordering.eq
  else if Nat.blt a b then Ordering.lt else Ordering.gt

def compareLexNatList (xs ys : List Nat) : Ordering :=
  match xs, ys with
  | [], [] => Ordering.eq
  | [], _  => Ordering.lt
  | _, []  => Ordering.gt
  | x::xs', y::ys' =>
    match cmpNat x y with
    | Ordering.lt => Ordering.lt
    | Ordering.gt => Ordering.gt
    | Ordering.eq => compareLexNatList xs' ys'

def minLength (list1 : List (List Nat)) : Nat × List Nat :=
  match list1 with
  | [] => (0, [])
  | x::xs =>
    xs.foldl
      (fun (acc : Nat × List Nat) (cur : List Nat) =>
        let accLen := acc.fst
        let accList := acc.snd
        let accLen' := Nat.min accLen cur.length
        let accList' :=
          match compareLexNatList cur accList with
          | Ordering.lt => cur
          | _ => accList
        (accLen', accList')
      )
      (x.length, x)

#guard minLength [[0], [1, 3], [5, 7], [9, 11], [13, 15, 17]] = (1, [0])
#guard minLength [[1], [5, 7], [10, 12, 14, 15]] = (1, [1])
#guard minLength [[5], [15, 20, 25]] = (1, [5])
