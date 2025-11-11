import Batteries
open Std

inductive PyVal where
  | dict (kvs : List (PyVal × PyVal)) : PyVal
  | nat (n : Nat) : PyVal
  | str (s : String) : PyVal
deriving Repr, BEq

mutual
  def dictDepth (d : PyVal) : Nat :=
    match d with
    | PyVal.dict kvs => 1 + listDepth kvs
    | _ => 0
  termination_by d => sizeOf d
  decreasing_by
    all_goals simp_wf

  def listDepth (kvs : List (PyVal × PyVal)) : Nat :=
    match kvs with
    | [] => 0
    | (_, v) :: xs =>
      Nat.max (dictDepth v) (listDepth xs)
  termination_by kvs => sizeOf kvs
  decreasing_by
    all_goals simp_wf
end

def ex1 : PyVal :=
  PyVal.dict
    [ (PyVal.str "a", PyVal.nat 1)
    , (PyVal.str "b", PyVal.dict
        [ (PyVal.str "c", PyVal.dict
            [ (PyVal.str "d", PyVal.dict []) ]) ]) ]

#guard dictDepth ex1 = 4

def ex2 : PyVal :=
  PyVal.dict
    [ (PyVal.str "a", PyVal.nat 1)
    , (PyVal.str "b", PyVal.dict
        [ (PyVal.str "c", PyVal.str "python") ]) ]

#guard dictDepth ex2 = 2

def ex3 : PyVal :=
  PyVal.dict
    [ (PyVal.nat 1, PyVal.str "Sun")
    , (PyVal.nat 2, PyVal.dict
        [ (PyVal.nat 3, PyVal.dict
            [ (PyVal.nat 4, PyVal.str "Mon") ]) ]) ]

#guard dictDepth ex3 = 3
