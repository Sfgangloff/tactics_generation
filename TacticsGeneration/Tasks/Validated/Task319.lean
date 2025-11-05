import Batteries

open Std

def find_long_word (text : String) : List String :=
  text.splitOn " " |>.filter (fun w => w.length = 5)

#guard find_long_word "Please move back to strem" == ["strem"]
#guard find_long_word "4K Ultra HD streaming player" == ["Ultra"]
#guard find_long_word "Streaming Media Player" == ["Media"]
