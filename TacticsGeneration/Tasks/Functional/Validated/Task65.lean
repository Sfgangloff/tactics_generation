import Batteries
open Std

inductive Nested where
  | num : Nat → Nested
  | list : List Nested → Nested
  deriving Repr

def nestedSum : Nested → Nat
  | .num n => n
  | .list xs => xs.foldl (fun acc el => acc + nestedSum el) 0

def recursiveListSum (dataList : List Nested) : Nat :=
  nestedSum (Nested.list dataList)

#guard recursiveListSum [Nested.num 1, Nested.num 2, Nested.list [Nested.num 3, Nested.num 4], Nested.list [Nested.num 5, Nested.num 6]] = 21
#guard recursiveListSum [Nested.num 7, Nested.num 10, Nested.list [Nested.num 15, Nested.num 14], Nested.list [Nested.num 19, Nested.num 41]] = 106
#guard recursiveListSum [Nested.num 10, Nested.num 20, Nested.list [Nested.num 30, Nested.num 40], Nested.list [Nested.num 50, Nested.num 60]] = 210
