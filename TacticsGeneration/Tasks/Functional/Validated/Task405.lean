import Batteries

open Std

inductive PyVal where
  | s : String → PyVal
  | i : Int → PyVal
deriving BEq, DecidableEq

def checkTuplex (tuplex : List PyVal) (tuple1 : PyVal) : Bool :=
  if tuplex.contains tuple1 then true else false

#guard checkTuplex [PyVal.s "w", PyVal.i 3, PyVal.s "r", PyVal.s "e", PyVal.s "s", PyVal.s "o", PyVal.s "u", PyVal.s "r", PyVal.s "c", PyVal.s "e"] (PyVal.s "r") == true
#guard checkTuplex [PyVal.s "w", PyVal.i 3, PyVal.s "r", PyVal.s "e", PyVal.s "s", PyVal.s "o", PyVal.s "u", PyVal.s "r", PyVal.s "c", PyVal.s "e"] (PyVal.s "5") == false
#guard checkTuplex [PyVal.s "w", PyVal.i 3, PyVal.s "r", PyVal.s "e", PyVal.s "s", PyVal.s "o", PyVal.s "u", PyVal.s "r", PyVal.s "c", PyVal.s "e"] (PyVal.i 3) == true
