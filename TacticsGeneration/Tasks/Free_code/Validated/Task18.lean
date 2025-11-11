import Batteries



/-!
  Auto-generated from task 18.
  Module: Task18
-/

open Std

namespace Task18

/-- Build a set of characters present in a string. -/
def charsToSet (s : String) : HashSet Char :=
  s.foldl (fun acc c => acc.insert c) ({} : HashSet Char)

/-- Remove characters from s1 that appear in s2. -/
def removeDirtyChars (s1 s2 : String) : String :=
  let bad := charsToSet s2
  s1.foldl (fun acc c => if bad.contains c then acc else acc.push c) ""

end Task18


-- Tests
open Task18

#guard removeDirtyChars "probasscurve" "pros" == "bacuve"
#guard removeDirtyChars "digitalindia" "talent" == "digiidi"
#guard removeDirtyChars "exoticmiles" "toxic" == "emles"
