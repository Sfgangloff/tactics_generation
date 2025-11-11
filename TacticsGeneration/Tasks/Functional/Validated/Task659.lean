import Batteries
open Std

private def getAt? {α} (xs : List α) (i : Nat) : Option α :=
  match xs.drop i with
  | [] => none
  | y :: _ => some y

def Repeat (x : List Int) : List Int := Id.run do
  let xs := x
  let size := xs.length
  let mut repeated : List Int := []
  for i in [0:size] do
    match getAt? xs i with
    | some xi =>
      let k := i + 1
      for j in [k:size] do
        match getAt? xs j with
        | some xj =>
          if xi == xj && !(repeated.contains xi) then
            repeated := repeated ++ [xi]
          else
            pure ()
        | none => pure ()
    | none => pure ()
  return repeated

#guard Repeat [10, 20, 30, 20, 20, 30, 40, 50, -20, 60, 60, -20, -20] == [20, 30, -20, 60]
#guard Repeat [-1, 1, -1, 8] == [-1]
#guard Repeat [1, 2, 3, 1, 2] == [1, 2]
