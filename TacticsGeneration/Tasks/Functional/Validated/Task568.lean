import Batteries
open Std

def emptyList (length : Nat) : List (Std.HashMap Nat Nat) :=
  List.replicate length (Std.HashMap.emptyWithCapacity (capacity := 0))

macro_rules
  | `(Std.HashMap.empty) => `(Std.HashMap.emptyWithCapacity (capacity := 0))

instance [BEq α] [Hashable α] [BEq β] : BEq (Std.HashMap α β) where
  beq m₁ m₂ :=
    let findInList (k : α) (xs : List (α × β)) : Option β :=
      match xs.find? (fun kv => kv.fst == k) with
      | some kv => some kv.snd
      | none => none
    let ok :=
      (m₁.toList).foldl (fun acc (kv : α × β) =>
        if acc then
          let k := kv.fst
          let v1 := kv.snd
          match findInList k (m₂.toList) with
          | some v2 => v1 == v2
          | none => false
        else
          false
      ) true
    ok && (m₁.size == m₂.size)

#guard emptyList 5 == List.replicate 5 (Std.HashMap.empty : Std.HashMap Nat Nat)
#guard emptyList 6 == List.replicate 6 (Std.HashMap.empty : Std.HashMap Nat Nat)
#guard emptyList 7 == List.replicate 7 (Std.HashMap.empty : Std.HashMap Nat Nat)
