import Batteries

open Std

def asciiValue (k : Char) : Nat := k.toNat

#guard asciiValue 'A' = 65
#guard asciiValue 'R' = 82
#guard asciiValue 'S' = 83
