import Batteries

open Std

def findDissimilar (l1 l2 : List Nat) : HashSet Nat := Id.run do
  let s1 := HashSet.ofList l1
  let s2 := HashSet.ofList l2
  let part1 := s1.filter (fun x => !(x ∈ s2))
  let part2 := s2.filter (fun x => !(x ∈ s1))
  let mut res := part1
  for x in part2.toList do
    res := res.insert x
  return res

#guard findDissimilar [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [3, 6, 7, 10]
#guard findDissimilar [1, 2, 3, 4] [7, 2, 3, 9] == HashSet.ofList [1, 4, 7, 9]
#guard findDissimilar [21, 11, 25, 26] [26, 34, 21, 36] == HashSet.ofList [34, 36, 11, 25]
