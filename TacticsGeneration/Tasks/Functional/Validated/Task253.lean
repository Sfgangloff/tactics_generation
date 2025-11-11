import Batteries

open Std

inductive PyVal where
  | int : Int -> PyVal
  | float : Float -> PyVal
  | str : String -> PyVal
  deriving Repr

def count_integer (list1 : List PyVal) : Nat := Id.run do
  let mut ctr := 0
  for i in list1 do
    match i with
    | PyVal.int _ => ctr := ctr + 1
    | _ => pure ()
  return ctr

#guard count_integer [PyVal.int 1, PyVal.int 2, PyVal.str "abc", PyVal.float (1.2 : Float)] = 2
#guard count_integer [PyVal.int 1, PyVal.int 2, PyVal.int 3] = 3
#guard count_integer [PyVal.int 1, PyVal.float (1.2 : Float), PyVal.int 4, PyVal.float (5.1 : Float)] = 2
