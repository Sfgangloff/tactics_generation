import Batteries
open Std

def lookupByKey {β} (xs : List (String × β)) (k : String) : Option β :=
  match xs with
  | [] => none
  | (k', v) :: xs' => if k = k' then some v else lookupByKey xs' k

def grouping_dictionary (l : List (String × Nat)) : Std.HashMap String (List Nat) :=
  l.foldl (fun d (kv : String × Nat) =>
    let k := kv.fst
    let v := kv.snd
    let vs := (lookupByKey (d.toList) k).getD []
    d.insert k (vs ++ [v])
  ) ({} : Std.HashMap String (List Nat))

instance instBEqHashMapStringListNat : BEq (Std.HashMap String (List Nat)) where
  beq m₁ m₂ :=
    if m₁.size == m₂.size then
      let ok := (m₁.toList.foldl (fun acc (kv : String × (List Nat)) =>
        let k := kv.fst
        let v := kv.snd
        let present :=
          match Task653.lookupByKey (m₂.toList) k with
          | some v2 => v == v2
          | none => false
        acc && present
      ) true)
      ok
    else
      false

#guard grouping_dictionary [("yellow", 1), ("blue", 2), ("yellow", 3), ("blue", 4), ("red", 1)] == Std.HashMap.ofList [("yellow", [1, 3]), ("blue", [2, 4]), ("red", [1])]
#guard grouping_dictionary [("yellow", 10), ("blue", 20), ("yellow", 30), ("blue", 40), ("red", 10)] == Std.HashMap.ofList [("yellow", [10, 30]), ("blue", [20, 40]), ("red", [10])]
#guard grouping_dictionary [("yellow", 15), ("blue", 25), ("yellow", 35), ("blue", 45), ("red", 15)] == Std.HashMap.ofList [("yellow", [15, 35]), ("blue", [25, 45]), ("red", [15])]
