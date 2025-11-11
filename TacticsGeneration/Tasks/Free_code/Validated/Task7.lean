import Batteries



/-!
  Auto-generated from task 7.
  Module: Task7
-/

open Std

def findCharLong (text : String) : List String :=
  text.splitOn " " |>.filter (fun w => w.length >= 4)


-- Tests
#guard findCharLong "Please move back to stream" == ["Please", "move", "back", "stream"]
#guard findCharLong "Jing Eco and Tech" == ["Jing", "Tech"]
#guard findCharLong "Jhingai wulu road Zone 3" == ["Jhingai", "wulu", "road", "Zone"]
