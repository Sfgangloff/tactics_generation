import Batteries

open Std

def extractSingly (testList : List (List Nat)) : List Nat := Id.run do
  let mut temp : HashSet Nat := HashSet.empty
  let mut res : Array Nat := #[]
  for inner in testList do
    for ele in inner do
      if !temp.contains ele then
        temp := temp.insert ele
        res := res.push ele
  return res.toList

#guard extractSingly [[3, 4, 5], [4, 5, 7], [1, 4]] == [3, 4, 5, 7, 1]
#guard extractSingly [[1, 2, 3], [4, 2, 3], [7, 8]] == [1, 2, 3, 4, 7, 8]
#guard extractSingly [[7, 8, 9], [10, 11, 12], [10, 11]] == [7, 8, 9, 10, 11, 12]
