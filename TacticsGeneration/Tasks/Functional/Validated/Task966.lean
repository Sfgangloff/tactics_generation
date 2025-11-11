import Batteries

open Std

inductive PyVal
| tup : List String → PyVal
| str : String → PyVal
deriving BEq, Repr

def removeEmpty (tuple1 : List PyVal) : List PyVal :=
  let tuple1 := tuple1.filter (fun t =>
    match t with
    | PyVal.tup xs => !xs.isEmpty
    | PyVal.str s => s != "")
  tuple1

#guard removeEmpty [PyVal.tup [], PyVal.tup [], PyVal.tup [""], PyVal.tup ["a","b"], PyVal.tup ["a","b","c"], PyVal.str "d"]
  == [PyVal.tup [""], PyVal.tup ["a","b"], PyVal.tup ["a","b","c"], PyVal.str "d"]
#guard removeEmpty [PyVal.tup [], PyVal.tup [], PyVal.tup [""], PyVal.str "python", PyVal.str "program"]
  == [PyVal.tup [""], PyVal.str "python", PyVal.str "program"]
#guard removeEmpty [PyVal.tup [], PyVal.tup [], PyVal.tup [""], PyVal.str "java"]
  == [PyVal.tup [""], PyVal.str "java"]
