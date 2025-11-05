import Batteries

open Std

def hashMapOfList (l : List (String × Nat)) : Std.HashMap String Nat :=
  l.foldl (fun m (kv) => m.insert kv.fst kv.snd) (Std.HashMap.empty : Std.HashMap String Nat)

def check_value (dict : Std.HashMap String Nat) (n : Nat) : Bool := Id.run do
  for (k, v) in dict do
    if v != n then return false
  return true

#guard check_value (hashMapOfList [("Cierra Vega", 12), ("Alden Cantrell", 12), ("Kierra Gentry", 12), ("Pierre Cox", 12)]) 10 = false
#guard check_value (hashMapOfList [("Cierra Vega", 12), ("Alden Cantrell", 12), ("Kierra Gentry", 12), ("Pierre Cox", 12)]) 12 = true
#guard check_value (hashMapOfList [("Cierra Vega", 12), ("Alden Cantrell", 12), ("Kierra Gentry", 12), ("Pierre Cox", 12)]) 5 = false
