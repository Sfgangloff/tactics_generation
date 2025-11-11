import Batteries



/-!
  Auto-generated from task 2.
  Module: Task2
-/

open Std

namespace Task2

/-- Find similar elements (set intersection) between two lists of integers.
    Returns a HashSet containing elements common to both lists. -/
def similarElements (l1 l2 : List Int) : HashSet Int :=
  let s1 : HashSet Int := HashSet.ofList l1
  let s2 : HashSet Int := HashSet.ofList l2
  s1.filter (fun x => s2.contains x)

end Task2


-- Tests
open Task2

#guard similarElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard similarElements [1, 2, 3, 4] [5, 4, 3, 7] == HashSet.ofList [3, 4]
#guard similarElements [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]
