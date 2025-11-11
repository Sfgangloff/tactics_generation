import Batteries

open Std

def greaterSpecificnum (list : List Nat) (num : Nat) : Bool :=
  list.all (fun x => Nat.ble num x)

#guard greaterSpecificnum [220, 330, 500] 200 == true
#guard greaterSpecificnum [12, 17, 21] 20 == false
#guard greaterSpecificnum [1, 2, 3, 4] 10 == false
