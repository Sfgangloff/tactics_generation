import Batteries

open Std

def insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

def isortBy {α : Type} (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy lt x acc) []

def sortDictItem (testDict : List ((Nat × Nat) × Nat)) : List ((Nat × Nat) × Nat) :=
  let keyProd (p : (Nat × Nat) × Nat) : Nat :=
    let k := p.fst
    k.fst * k.snd
  isortBy (fun a b => keyProd a < keyProd b) testDict

#guard sortDictItem [((5, 6), 3), ((2, 3), 9), ((8, 4), 10), ((6, 4), 12)] == [((2, 3), 9), ((6, 4), 12), ((5, 6), 3), ((8, 4), 10)]
#guard sortDictItem [((6, 7), 4), ((3, 4), 10), ((9, 5), 11), ((7, 5), 13)] == [((3, 4), 10), ((7, 5), 13), ((6, 7), 4), ((9, 5), 11)]
#guard sortDictItem [((7, 8), 5), ((4, 5), 11), ((10, 6), 12), ((8, 6), 14)] == [((4, 5), 11), ((8, 6), 14), ((7, 8), 5), ((10, 6), 12)]
