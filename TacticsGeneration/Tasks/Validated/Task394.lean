import Batteries

open Std

def checkDistinct (testTup : List Nat) : Bool := Id.run do
  let mut res := true
  let mut temp : HashSet Nat := HashSet.empty
  for ele in testTup do
    if ele ∈ temp then
      res := false
      return res
    else
      temp := temp.insert ele
  return res

#guard checkDistinct [1, 4, 5, 6, 1, 4] == false
#guard checkDistinct [1, 4, 5, 6] == true
#guard checkDistinct [2, 3, 4, 5, 6] == true
