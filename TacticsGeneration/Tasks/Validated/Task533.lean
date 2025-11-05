import Batteries
open Std

inductive DataType where
  | int
  | str
  | float
  deriving BEq, DecidableEq, Repr

inductive DataVal where
  | intVal (i : Int)
  | strVal (s : String)
  | floatVal (f : Float)
  deriving BEq, Repr

def isInstanceOf (v : DataVal) (t : DataType) : Bool :=
  match v, t with
  | .intVal _, .int => true
  | .strVal _, .str => true
  | .floatVal _, .float => true
  | _, _ => false

def removeDatatype (testTuple : List DataVal) (dataType : DataType) : List DataVal := Id.run do
  let mut res : Array DataVal := #[]
  for ele in testTuple do
    if !(isInstanceOf ele dataType) then
      res := res.push ele
  return res.toList

#guard removeDatatype [DataVal.intVal 4, DataVal.intVal 5, DataVal.intVal 4, DataVal.floatVal 7.7, DataVal.floatVal 1.2] DataType.int == [DataVal.floatVal 7.7, DataVal.floatVal 1.2]
#guard removeDatatype [DataVal.intVal 7, DataVal.intVal 8, DataVal.intVal 9, DataVal.strVal "SR"] DataType.str == [DataVal.intVal 7, DataVal.intVal 8, DataVal.intVal 9]
#guard removeDatatype [DataVal.intVal 7, DataVal.floatVal 1.1, DataVal.intVal 2, DataVal.floatVal 2.2] DataType.float == [DataVal.intVal 7, DataVal.intVal 2]
