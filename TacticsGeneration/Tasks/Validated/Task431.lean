import Batteries

open Std

def commonElement [BEq α] (list1 list2 : List α) : Option Bool := Id.run do
  let mut result := false
  for x in list1 do
    for y in list2 do
      if x == y then
        result := true
        return some result
  return none

#guard commonElement [1,2,3,4,5] [5,6,7,8,9] == some true
#guard commonElement [1,2,3,4,5] [6,7,8,9] == none
#guard commonElement ["a","b","c"] ["d","b","e"] == some true
