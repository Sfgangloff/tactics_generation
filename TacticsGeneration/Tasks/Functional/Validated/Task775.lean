import Batteries

open Std

def oddPosition (nums : List Nat) : Bool :=
  let rec go (l : List Nat) (i : Nat) : Bool :=
    match l with
    | [] => true
    | x :: xs => (x % 2 == i % 2) && go xs (i + 1)
  go nums 0

#guard oddPosition [2,1,4,3,6,7,6,3] == true
#guard oddPosition [4,1,2] == true
#guard oddPosition [1,2,3] == false
