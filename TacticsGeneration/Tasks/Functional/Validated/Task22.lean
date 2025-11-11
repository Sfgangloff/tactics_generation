import Batteries

open Std

def findFirstDuplicate (nums : List Int) : Int := Id.run do
  let mut numSet := HashSet.empty
  let noDuplicate := -1
  for num in nums do
    if numSet.contains num then
      return num
    else
      numSet := numSet.insert num
  return noDuplicate

#guard findFirstDuplicate [1, 2, 3, 4, 4, 5] == 4
#guard findFirstDuplicate [1, 2, 3, 4] == -1
#guard findFirstDuplicate [1, 1, 2, 3, 3, 2, 2] == 1
