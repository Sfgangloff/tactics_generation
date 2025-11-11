import Batteries

open Std

def multipleToSingle (L : List Int) : Int :=
  let s := L.foldl (fun acc x => acc ++ toString x) ""
  match s.toInt? with
  | some v => v
  | none => 0

#guard multipleToSingle [11, 33, 50] == 113350
#guard multipleToSingle [-1, 2, 3, 4, 5, 6] == -123456
#guard multipleToSingle [10, 15, 20, 25] == 10152025
