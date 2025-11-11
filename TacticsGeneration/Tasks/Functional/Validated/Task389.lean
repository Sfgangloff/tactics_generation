import Batteries

open Std

def findLucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | n+2 => findLucas (n+1) + findLucas n

#guard findLucas 9 = 76
#guard findLucas 4 = 7
#guard findLucas 3 = 4
