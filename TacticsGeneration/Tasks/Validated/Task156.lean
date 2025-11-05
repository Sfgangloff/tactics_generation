import Batteries

open Std

def charToDigit (c : Char) : Nat := c.toNat - '0'.toNat

def parseNat (s : String) : Nat :=
  s.data.foldl (fun acc c => acc * 10 + charToDigit c) 0

def tupleIntStr (tupleStr : List (String × String)) : List (Nat × Nat) :=
  tupleStr.map (fun x => (parseNat x.fst, parseNat x.snd))

#guard tupleIntStr [("333", "33"), ("1416", "55")] = [(333, 33), (1416, 55)]
#guard tupleIntStr [("999", "99"), ("1000", "500")] = [(999, 99), (1000, 500)]
#guard tupleIntStr [("666", "66"), ("1500", "555")] = [(666, 66), (1500, 555)]
