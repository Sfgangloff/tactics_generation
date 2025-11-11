import Batteries

open Std

def sameOrder (l1 l2 : List String) : Bool :=
  let s1 := HashSet.ofList l1
  let s2 := HashSet.ofList l2
  let common := s1.filter (fun x => x ∈ s2)
  let l1f := l1.filter (fun e => e ∈ common)
  let l2f := l2.filter (fun e => e ∈ common)
  l1f == l2f

#guard sameOrder ["red","green","black","orange"] ["red","pink","green","white","black"] == true
#guard sameOrder ["red","pink","green","white","black"] ["white","orange","pink","black"] == false
#guard sameOrder ["red","green","black","orange"] ["red","pink","green","white","black"] == true
