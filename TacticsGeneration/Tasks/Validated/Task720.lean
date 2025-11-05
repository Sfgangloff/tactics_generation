import Batteries

open Std

inductive NatOrDict where
  | nat (n : Nat)
  | dict (d : List (String × Nat))
  deriving Repr, DecidableEq

def addDictToTuple (test_tup : List Nat) (test_dict : List (String × Nat)) : List NatOrDict :=
  let test_tup := test_tup.map NatOrDict.nat
  let test_tup := test_tup.concat (NatOrDict.dict test_dict)
  test_tup

#guard addDictToTuple [4, 5, 6] [("MSAM", 1), ("is", 2), ("best", 3)] = [NatOrDict.nat 4, NatOrDict.nat 5, NatOrDict.nat 6, NatOrDict.dict [("MSAM", 1), ("is", 2), ("best", 3)]]
#guard addDictToTuple [1, 2, 3] [("UTS", 2), ("is", 3), ("Worst", 4)] = [NatOrDict.nat 1, NatOrDict.nat 2, NatOrDict.nat 3, NatOrDict.dict [("UTS", 2), ("is", 3), ("Worst", 4)]]
#guard addDictToTuple [8, 9, 10] [("POS", 3), ("is", 4), ("Okay", 5)] = [NatOrDict.nat 8, NatOrDict.nat 9, NatOrDict.nat 10, NatOrDict.dict [("POS", 3), ("is", 4), ("Okay", 5)]]
