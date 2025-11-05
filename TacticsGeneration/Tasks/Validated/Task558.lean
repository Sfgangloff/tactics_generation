import Batteries

open Std

def digitDistanceNums (n1 n2 : Int) : Nat :=
  let d : Nat := Int.natAbs (n1 - n2)
  let s := toString d
  s.data.foldl (fun acc c => acc + (c.toNat - ('0').toNat)) 0

#guard digitDistanceNums 1 2 == 1
#guard digitDistanceNums 23 56 == 6
#guard digitDistanceNums 123 256 == 7
