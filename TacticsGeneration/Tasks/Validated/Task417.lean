import Batteries

open Std

private def updateOrInsert (out : List (String × List String)) (k : String) (tail : List String) : List (String × List String) :=
  let rec go (xs : List (String × List String)) : (List (String × List String) × Bool) :=
    match xs with
    | [] => ([], false)
    | (k', v) :: xs' =>
      let (rest, found) := go xs'
      if k' == k then
        ((k', v ++ tail) :: rest, true)
      else
        ((k', v) :: rest, found)
  let (res, found) := go out
  if found then res else res ++ [(k, k :: tail)]

def groupTuples (input : List (List String)) : List (List String) := Id.run do
  let mut outPairs : List (String × List String) := []
  for elem in input do
    match elem with
    | [] => ()
    | h :: t => outPairs := updateOrInsert outPairs h t
  return outPairs.map (fun p => p.snd)

#guard groupTuples [["x", "y"], ["x", "z"], ["w", "t"]] = [["x", "y", "z"], ["w", "t"]]
#guard groupTuples [["a", "b"], ["a", "c"], ["d", "e"]] = [["a", "b", "c"], ["d", "e"]]
#guard groupTuples [["f", "g"], ["f", "g"], ["h", "i"]] = [["f", "g", "g"], ["h", "i"]]
