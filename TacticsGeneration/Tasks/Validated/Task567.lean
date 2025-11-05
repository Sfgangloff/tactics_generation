import Batteries

open Std

def issortList (list1 : List Nat) : Bool :=
  let rec go (l : List Nat) : Bool :=
    match l with
    | [] => true
    | _ :: [] => true
    | x :: y :: rest => if Nat.ble x y then go (y :: rest) else false
  go list1

#guard issortList [1,2,4,6,8,10,12,14,16,17] == true
#guard issortList [1, 2, 4, 6, 8, 10, 12, 14, 20, 17] == false
#guard issortList [1, 2, 4, 6, 8, 10, 15, 14, 20] == false
