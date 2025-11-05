import Batteries

open Std

def concatenate_elements (list : List String) : String :=
  list.foldl (fun ans i => ans ++ " " ++ i) " "

#guard concatenate_elements ["hello","there","have","a","rocky","day"] == "  hello there have a rocky day"
#guard concatenate_elements ["Hi","there","How","are","you"] == "  Hi there How are you"
#guard concatenate_elements ["Part","of","the","journey","is","end"] == "  Part of the journey is end"
