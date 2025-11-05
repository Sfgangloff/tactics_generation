import Batteries

open Std

def exchangeElements (lst : List Nat) : List Nat :=
  let rec go (l accRev : List Nat) : List Nat :=
    match l with
    | a :: b :: t => go t (a :: b :: accRev)
    | a :: [] => a :: accRev
    | [] => accRev
  (go lst []).reverse

#guard exchangeElements [0,1,2,3,4,5] = [1,0,3,2,5,4]
#guard exchangeElements [5,6,7,8,9,10] = [6,5,8,7,10,9]
#guard exchangeElements [25,35,45,55,75,95] = [35,25,55,45,95,75]
