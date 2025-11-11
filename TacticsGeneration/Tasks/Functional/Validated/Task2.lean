import Batteries

open Std

def similarElements (l1 l2 : List Int) : HashSet Int := Id.run do
  let s1 := HashSet.ofList l1
  let s2 := HashSet.ofList l2
  return s1.filter (fun x => x ∈ s2)

#guard similarElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard similarElements [1, 2, 3, 4] [5, 4, 3, 7] == HashSet.ofList [3, 4]
#guard similarElements [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]
