import Batteries
open Std

def pow10 : Nat → Float
  | 0 => 1.0
  | n+1 => pow10 n * 10.0

def parseSimpleFloat (s : String) : Option Float :=
  let neg := s.startsWith "-"
  let core := if neg then s.drop 1 else s
  let parts := core.splitOn "."
  match parts with
  | [intStr] =>
      match intStr.toInt? with
      | some i =>
          let base := Float.ofInt i
          some (if neg then -base else base)
      | none => none
  | [intStr, fracStr] =>
      match intStr.toInt?, fracStr.toNat? with
      | some i, some n =>
          let base := Float.ofInt i
          let denom := pow10 fracStr.length
          let frac := (Float.ofInt (Int.ofNat n)) / denom
          let total := base + frac
          some (if neg then -total else total)
      | _, _ => none
  | _ => none

def floatToTuple (test_str : String) : List Float :=
  (test_str.splitOn ", ").map (fun s => (parseSimpleFloat s).getD 0.0)

#guard floatToTuple "1.2, 1.3, 2.3, 2.4, 6.5" == [1.2, 1.3, 2.3, 2.4, 6.5]
#guard floatToTuple "2.3, 2.4, 5.6, 5.4, 8.9" == [2.3, 2.4, 5.6, 5.4, 8.9]
#guard floatToTuple "0.3, 0.5, 7.8, 9.4" == [0.3, 0.5, 7.8, 9.4]
