import Batteries
open Std

def isSamepatterns (colors : List String) (patterns : List String) : Bool := Id.run do
  if colors.length != patterns.length then
    return false
  let mut assoc : List (String × List String) := []
  let mut pset : HashSet String := HashSet.emptyWithCapacity 0
  let mut sset : HashSet String := HashSet.emptyWithCapacity 0
  let len := patterns.length
  for i in [0 : len] do
    let p := patterns.getD i ""
    let c := colors.getD i ""
    pset := pset.insert p
    sset := sset.insert c
    let rec appendAt (xs : List (String × List String)) : List (String × List String) :=
      match xs with
      | [] => [(p, [c])]
      | (k, vs) :: rest =>
        if k = p then
          (k, vs ++ [c]) :: rest
        else
          (k, vs) :: appendAt rest
    assoc := appendAt assoc
  if pset.size != sset.size then
    return false
  for kv in assoc do
    let values := kv.snd
    let rec allEqual (lst : List String) (prev? : Option String) : Bool :=
      match lst with
      | [] => true
      | x :: xs =>
        match prev? with
        | none => allEqual xs (some x)
        | some y => if x = y then allEqual xs (some y) else false
    if !(allEqual values none) then
      return false
  return true

#guard isSamepatterns ["red","green","green"] ["a", "b", "b"] == true
#guard isSamepatterns ["red","green","greenn"] ["a","b","b"] == false
#guard isSamepatterns ["red","green","greenn"] ["a","b"] == false
