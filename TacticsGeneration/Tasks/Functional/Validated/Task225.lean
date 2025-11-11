import Batteries
open Std

def listGet (xs : List Nat) (i : Nat) : Nat :=
  let rec go (xs : List Nat) (i : Nat) : Nat :=
    match xs, i with
    | [], _ => 0
    | x :: _, 0 => x
    | _ :: xs', Nat.succ i' => go xs' i'
  go xs i

def find_Min (arr : List Nat) (low high : Nat) : Nat := Id.run do
  let mut lo := low
  let mut hi := high
  while lo < hi do
    let mid := lo + (hi - lo) / 2
    if listGet arr mid == listGet arr hi then
      hi := hi - 1
    else if listGet arr mid > listGet arr hi then
      lo := mid + 1
    else
      hi := mid
  return listGet arr hi

#guard find_Min [1,2,3,4,5] 0 4 = 1
#guard find_Min [4,6,8] 0 2 = 4
#guard find_Min [2,3,5,7,9] 0 4 = 2
