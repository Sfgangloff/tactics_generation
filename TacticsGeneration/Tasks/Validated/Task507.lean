import Batteries

open Std

def removeWords (list1 : List String) (removewords : List String) : List String := Id.run do
  
  let copy := list1
  let mut res := list1
  for word in copy do
    if removewords.contains word then
      res := res.erase word
  return res

#guard removeWords ["red", "green", "blue", "white", "black", "orange"] ["white", "orange"] == ["red", "green", "blue", "black"]
#guard removeWords ["red", "green", "blue", "white", "black", "orange"] ["black", "orange"] == ["red", "green", "blue", "white"]
#guard removeWords ["red", "green", "blue", "white", "black", "orange"] ["blue", "white"] == ["red", "green", "black", "orange"]
