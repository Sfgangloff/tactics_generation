import Batteries
open Std

def find? [BEq α] [Hashable α] (m : HashMap α β) (k : α) : Option β :=
  m.fold (init := (none : Option β)) (fun acc a b =>
    match acc with
    | some _ => acc
    | none => if a == k then some b else none)

def groupKeyvalue (l : List (String × Nat)) : Std.HashMap String (List Nat) := Id.run do
  let mut m : Std.HashMap String (List Nat) := {}
  for (k, v) in l do
    let old :=
      match m.find? k with
      | some xs => xs
      | none => []
    m := m.insert k (old ++ [v])
  return m

#guard (
  (match (Task174.groupKeyvalue [("yellow", 1), ("blue", 2), ("yellow", 3), ("blue", 4), ("red", 1)]).find? "yellow" with | some xs => xs | none => []) == [1, 3]
  &&
  (match (Task174.groupKeyvalue [("yellow", 1), ("blue", 2), ("yellow", 3), ("blue", 4), ("red", 1)]).find? "blue" with | some xs => xs | none => []) == [2, 4]
  &&
  (match (Task174.groupKeyvalue [("yellow", 1), ("blue", 2), ("yellow", 3), ("blue", 4), ("red", 1)]).find? "red" with | some xs => xs | none => []) == [1]
  &&
  ((Task174.groupKeyvalue [("yellow", 1), ("blue", 2), ("yellow", 3), ("blue", 4), ("red", 1)]).toList.length == 3)
)

#guard (
  (match (Task174.groupKeyvalue [("python", 1), ("python", 2), ("python", 3), ("python", 4), ("python", 5)]).find? "python" with | some xs => xs | none => []) == [1,2,3,4,5]
  &&
  ((Task174.groupKeyvalue [("python", 1), ("python", 2), ("python", 3), ("python", 4), ("python", 5)]).toList.length == 1)
)

#guard (
  (match (Task174.groupKeyvalue [("yellow",100), ("blue", 200), ("yellow", 300), ("blue", 400), ("red", 100)]).find? "yellow" with | some xs => xs | none => []) == [100, 300]
  &&
  (match (Task174.groupKeyvalue [("yellow",100), ("blue", 200), ("yellow", 300), ("blue", 400), ("red", 100)]).find? "blue" with | some xs => xs | none => []) == [200, 400]
  &&
  (match (Task174.groupKeyvalue [("yellow",100), ("blue", 200), ("yellow", 300), ("blue", 400), ("red", 100)]).find? "red" with | some xs => xs | none => []) == [100]
  &&
  ((Task174.groupKeyvalue [("yellow",100), ("blue", 200), ("yellow", 300), ("blue", 400), ("red", 100)]).toList.length == 3)
)
