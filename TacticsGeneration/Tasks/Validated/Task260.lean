import Batteries

open Std

def newmanPrime : Nat -> Nat
| 0 => 1
| 1 => 1
| n+2 => 2 * newmanPrime (n+1) + newmanPrime n

#guard newmanPrime 3 = 7
#guard newmanPrime 4 = 17
#guard newmanPrime 5 = 41
