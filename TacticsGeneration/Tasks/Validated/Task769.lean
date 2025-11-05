import Batteries

open Std

def Diff (li1 li2 : List Nat) : HashSet Nat := Id.run do
  let s1 := HashSet.ofList li1
  let s2 := HashSet.ofList li2
  let all := HashSet.ofList (li1 ++ li2)
  return all.filter (fun x => (s1.contains x && !(s2.contains x)) || (s2.contains x && !(s1.contains x)))

#guard Diff [10, 15, 20, 25, 30, 35, 40] [25, 40, 35] == HashSet.ofList [10, 20, 30, 15]
#guard Diff [1,2,3,4,5] [6,7,1] == HashSet.ofList [2,3,4,5,6,7]
#guard Diff [1,2,3] [6,7,1] == HashSet.ofList [2,3,6,7]
