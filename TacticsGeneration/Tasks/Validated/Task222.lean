import Batteries

open Std

inductive PyVal where
| int : Nat → PyVal
| str : String → PyVal
deriving BEq, Repr

def sameTag (a b : PyVal) : Bool :=
  match a, b with
  | .int _, .int _ => true
  | .str _, .str _ => true
  | _, _ => false

def checkType (testTuple : List PyVal) : Bool := Id.run do
  let mut res := true
  match testTuple with
  | [] => return true 
  | first :: rest =>
    for ele in rest do
      if !(sameTag ele first) then
        res := false
        break
    return res

#guard checkType [PyVal.int 5, PyVal.int 6, PyVal.int 7, PyVal.int 3, PyVal.int 5, PyVal.int 6] = true
#guard checkType [PyVal.int 1, PyVal.int 2, PyVal.str "4"] = false
#guard checkType [PyVal.int 3, PyVal.int 2, PyVal.int 1, PyVal.int 4, PyVal.int 5] = true
