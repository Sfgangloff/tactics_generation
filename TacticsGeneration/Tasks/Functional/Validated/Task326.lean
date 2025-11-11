import Batteries
open Std

private def incrKey (w : String) (xs : List (String × Nat)) : (List (String × Nat)) × Bool :=
  match xs with
  | [] => ([(w, 1)], false)
  | (k2, v) :: t =>
    if k2 == w then
      ((k2, v + 1) :: t, true)
    else
      let (t', found) := incrKey w t
      ((k2, v) :: t', found)

def mostOccurrences (testList : List String) : String := Id.run do
  let mut temp : List (String × Nat) := []
  for sub in testList do
    let words := sub.splitOn " "
    for wrd in words do
      if wrd == "" then
        continue
      let (newTemp, _) := incrKey wrd temp
      temp := newTemp
  match temp with
  | [] => return ""
  | (k0, v0) :: t =>
    let mut bestKey := k0
    let mut bestVal := v0
    for (k, v) in t do
      if v > bestVal then
        bestVal := v
        bestKey := k
    return bestKey

#guard mostOccurrences ["UTS is best for RTF", "RTF love UTS", "UTS is best"] == "UTS"
#guard mostOccurrences ["Its been a great year", "this year is so worse", "this year is okay"] == "year"
#guard mostOccurrences ["Families can be reunited", "people can be reunited", "Tasks can be achieved "] == "can"
