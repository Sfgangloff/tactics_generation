import Batteries

open Std

def isOctagonal (n : Nat) : Nat := 3 * n * n - 2 * n

#guard isOctagonal 5 == 65
#guard isOctagonal 10 == 280
#guard isOctagonal 15 == 645
