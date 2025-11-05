import Batteries
open Std

private def lookupOr (m : Std.HashMap String Nat) (k : String) (default : Nat) : Nat :=
  let rec go (l : List (String × Nat)) : Nat :=
    match l with
    | [] => default
    | (k', v') :: t => if k' == k then v' else go t
  go m.toList

def addDict (d1 d2 : Std.HashMap String Nat) : Std.HashMap String Nat := Id.run do
  let mut res := d1
  for (k, v) in d2.toList do
    let prev := lookupOr res k 0
    res := res.insert k (prev + v)
  return res

def HashMap.findD {α β} [BEq α] [Hashable α] (m : Std.HashMap α β) (a : α) (default : β) : β :=
  let rec go (l : List (α × β)) : Option β :=
    match l with
    | [] => none
    | (k, v) :: t => if k == a then some v else go t
  match go m.toList with
  | some v => v
  | none => default

#guard (addDict (Std.HashMap.ofList [("a", 100), ("b", 200), ("c", 300)]) (Std.HashMap.ofList [("a", 300), ("b", 200), ("d", 400)])).size = 4
#guard (addDict (Std.HashMap.ofList [("a", 100), ("b", 200), ("c", 300)]) (Std.HashMap.ofList [("a", 300), ("b", 200), ("d", 400)])).findD "a" 0 = 400
#guard (addDict (Std.HashMap.ofList [("a", 100), ("b", 200), ("c", 300)]) (Std.HashMap.ofList [("a", 300), ("b", 200), ("d", 400)])).findD "b" 0 = 400
#guard (addDict (Std.HashMap.ofList [("a", 100), ("b", 200), ("c", 300)]) (Std.HashMap.ofList [("a", 300), ("b", 200), ("d", 400)])).findD "c" 0 = 300
#guard (addDict (Std.HashMap.ofList [("a", 100), ("b", 200), ("c", 300)]) (Std.HashMap.ofList [("a", 300), ("b", 200), ("d", 400)])).findD "d" 0 = 400

#guard (addDict (Std.HashMap.ofList [("a", 500), ("b", 700), ("c", 900)]) (Std.HashMap.ofList [("a", 500), ("b", 600), ("d", 900)])).size = 4
#guard (addDict (Std.HashMap.ofList [("a", 500), ("b", 700), ("c", 900)]) (Std.HashMap.ofList [("a", 500), ("b", 600), ("d", 900)])).findD "a" 0 = 1000
#guard (addDict (Std.HashMap.ofList [("a", 500), ("b", 700), ("c", 900)]) (Std.HashMap.ofList [("a", 500), ("b", 600), ("d", 900)])).findD "b" 0 = 1300
#guard (addDict (Std.HashMap.ofList [("a", 500), ("b", 700), ("c", 900)]) (Std.HashMap.ofList [("a", 500), ("b", 600), ("d", 900)])).findD "c" 0 = 900
#guard (addDict (Std.HashMap.ofList [("a", 500), ("b", 700), ("c", 900)]) (Std.HashMap.ofList [("a", 500), ("b", 600), ("d", 900)])).findD "d" 0 = 900

#guard (addDict (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)]) (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)])).size = 3
#guard (addDict (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)]) (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)])).findD "a" 0 = 1800
#guard (addDict (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)]) (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)])).findD "b" 0 = 1800
#guard (addDict (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)]) (Std.HashMap.ofList [("a", 900), ("b", 900), ("d", 900)])).findD "d" 0 = 1800
