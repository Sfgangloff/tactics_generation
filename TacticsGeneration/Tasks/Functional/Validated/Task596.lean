import Batteries

open Std

inductive PyVal where
  | N : Nat → PyVal
  | S : String → PyVal
  | T : List PyVal → PyVal

deriving instance Inhabited for PyVal

def tupleSize (tuple_list : PyVal) : Nat :=
  match tuple_list with
  | PyVal.T xs => xs.length
  | _ => 0

def pyGetSizeOf (x : PyVal) : Nat :=
  tupleSize x

#guard tupleSize (PyVal.T [PyVal.S "A", PyVal.N 1, PyVal.S "B", PyVal.N 2, PyVal.S "C", PyVal.N 3])
       = pyGetSizeOf (PyVal.T [PyVal.S "A", PyVal.N 1, PyVal.S "B", PyVal.N 2, PyVal.S "C", PyVal.N 3])
#guard tupleSize (PyVal.T [PyVal.N 1, PyVal.S "Raju", PyVal.N 2, PyVal.S "Nikhil", PyVal.N 3, PyVal.S "Deepanshu"])
       = pyGetSizeOf (PyVal.T [PyVal.N 1, PyVal.S "Raju", PyVal.N 2, PyVal.S "Nikhil", PyVal.N 3, PyVal.S "Deepanshu"])
#guard tupleSize (PyVal.T [
         PyVal.T [PyVal.N 1, PyVal.S "Lion"],
         PyVal.T [PyVal.N 2, PyVal.S "Tiger"],
         PyVal.T [PyVal.N 3, PyVal.S "Fox"],
         PyVal.T [PyVal.N 4, PyVal.S "Wolf"]
       ])
       = pyGetSizeOf (PyVal.T [
         PyVal.T [PyVal.N 1, PyVal.S "Lion"],
         PyVal.T [PyVal.N 2, PyVal.S "Tiger"],
         PyVal.T [PyVal.N 3, PyVal.S "Fox"],
         PyVal.T [PyVal.N 4, PyVal.S "Wolf"]
       ])
