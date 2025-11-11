import Batteries

open Std

def get_noOfways : Nat -> Nat
| 0 => 0
| 1 => 1
| Nat.succ (Nat.succ k) => get_noOfways (Nat.succ k) + get_noOfways k

#guard get_noOfways 4 = 3
#guard get_noOfways 3 = 2
#guard get_noOfways 5 = 5
