import Batteries
open Std

def is_Product_Even (arr : List Nat) (n : Nat) : Bool :=
  let rec go (xs : List Nat) (k : Nat) : Bool :=
    match xs, k with
    | _, 0 => false
    | [], _ => false
    | x :: xs', Nat.succ k' =>
      if (x &&& 1) == 0 then true else go xs' k'
  go arr n

#guard is_Product_Even [1,2,3] 3 == true
#guard is_Product_Even [1,2,1,4] 4 == true
#guard is_Product_Even [1,1] 2 == false
