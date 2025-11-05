import Batteries

open Std

def findLongWords (text : String) : List String :=
  text.splitOn.filter (fun x => x.length >= 4)

#guard findLongWords "Please move back to stream" == ["Please", "move", "back", "stream"]
#guard findLongWords "Jing Eco and Tech" == ["Jing", "Tech"]
#guard findLongWords "Jhingai wulu road Zone 3" == ["Jhingai", "wulu", "road", "Zone"]
