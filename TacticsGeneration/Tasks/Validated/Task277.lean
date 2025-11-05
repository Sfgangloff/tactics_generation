import Batteries

open Std

def dictFilter (dict : List (String × Nat)) (n : Nat) : List (String × Nat) :=
  dict.filter (fun kv => kv.snd >= n)

#guard HashSet.ofList (dictFilter [("Cierra Vega", 175), ("Alden Cantrell", 180), ("Kierra Gentry", 165), ("Pierre Cox", 190)] 170) == HashSet.ofList [("Cierra Vega", 175), ("Alden Cantrell", 180), ("Pierre Cox", 190)]
#guard HashSet.ofList (dictFilter [("Cierra Vega", 175), ("Alden Cantrell", 180), ("Kierra Gentry", 165), ("Pierre Cox", 190)] 180) == HashSet.ofList [("Alden Cantrell", 180), ("Pierre Cox", 190)]
#guard HashSet.ofList (dictFilter [("Cierra Vega", 175), ("Alden Cantrell", 180), ("Kierra Gentry", 165), ("Pierre Cox", 190)] 190) == HashSet.ofList [("Pierre Cox", 190)]
