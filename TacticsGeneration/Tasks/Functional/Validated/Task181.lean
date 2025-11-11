import Batteries

open Std

private def lcpLenAux (l1 l2 : List Char) (acc : Nat) : Nat :=
  match l1, l2 with
  | c1 :: t1, c2 :: t2 =>
    if c1 == c2 then lcpLenAux t1 t2 (acc + 1) else acc
  | _, _ => acc

def commonPrefixUtil (str1 str2 : String) : String :=
  let k := lcpLenAux str1.data str2.data 0
  str1.take k

def commonPrefix (arr : List String) (n : Nat) : String :=
  let taken := arr.take n
  match taken with
  | [] => ""
  | p :: xs => xs.foldl (fun acc s => commonPrefixUtil acc s) p

#guard commonPrefix ["tablets", "tables", "taxi", "tamarind"] 4 = "ta"
#guard commonPrefix ["apples", "ape", "april"] 3 = "ap"
#guard commonPrefix ["teens", "teenager", "teenmar"] 3 = "teen"
