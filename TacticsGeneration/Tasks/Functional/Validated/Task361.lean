import Batteries

open Std

inductive PyVal where
  | str (s : String)
  | list (xs : List Nat)
  deriving Repr, BEq, DecidableEq

def truthy : PyVal → Bool
  | .str s => s.length != 0
  | .list xs => !xs.isEmpty

def removeEmpty (list1 : List PyVal) : List PyVal :=
  list1.filter truthy

#guard removeEmpty [PyVal.list [], PyVal.list [], PyVal.list [], PyVal.str "Red", PyVal.str "Green", PyVal.list [1,2], PyVal.str "Blue", PyVal.list [], PyVal.list []] = [PyVal.str "Red", PyVal.str "Green", PyVal.list [1, 2], PyVal.str "Blue"]
#guard removeEmpty [PyVal.list [], PyVal.list [], PyVal.list [], PyVal.list [], PyVal.list [], PyVal.str "Green", PyVal.list [1,2], PyVal.str "Blue", PyVal.list [], PyVal.list []] = [PyVal.str "Green", PyVal.list [1, 2], PyVal.str "Blue"]
#guard removeEmpty [PyVal.list [], PyVal.list [], PyVal.list [], PyVal.str "Python", PyVal.list [], PyVal.list [], PyVal.str "programming", PyVal.str "language", PyVal.list [], PyVal.list [], PyVal.list [], PyVal.list [], PyVal.list []] = [PyVal.str "Python", PyVal.str "programming", PyVal.str "language"]
