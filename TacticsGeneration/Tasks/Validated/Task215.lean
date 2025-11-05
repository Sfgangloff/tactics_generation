import Batteries
open Std

inductive Encoded (α : Type) where
| single : α → Encoded α
| run : Nat → α → Encoded α

def decode_list {α : Type} (alist : List (Encoded α)) : List α :=
  alist.foldr
    (fun g acc =>
      match g with
      | Encoded.single x => x :: acc
      | Encoded.run n x => (List.replicate n x) ++ acc)
    []

#guard decode_list [Encoded.run 2 1, Encoded.single 2, Encoded.single 3, Encoded.run 2 4, Encoded.single 5, Encoded.single 1] = [1,1,2,3,4,4,5,1]
#guard decode_list [Encoded.single "a", Encoded.single "u", Encoded.single "t", Encoded.single "o", Encoded.single "m", Encoded.single "a", Encoded.single "t", Encoded.single "i", Encoded.single "c", Encoded.single "a", Encoded.run 2 "l", Encoded.single "y"] = ["a", "u", "t", "o", "m", "a", "t", "i", "c", "a", "l", "l", "y"]
#guard decode_list [Encoded.single "p", Encoded.single "y", Encoded.single "t", Encoded.single "h", Encoded.single "o", Encoded.single "n"] = ["p", "y", "t", "h", "o", "n"]
