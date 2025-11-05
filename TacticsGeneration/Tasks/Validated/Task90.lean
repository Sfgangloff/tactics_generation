import Batteries

open Std

def lenLog (list1 : List String) : Nat :=
  let initialMax := (list1.headD "").length
  list1.foldl (fun maxLen i => if i.length > maxLen then i.length else maxLen) initialMax

#guard lenLog ["python","PHP","bigdata"] == 7
#guard lenLog ["a","ab","abc"] == 3
#guard lenLog ["small","big","tall"] == 5
