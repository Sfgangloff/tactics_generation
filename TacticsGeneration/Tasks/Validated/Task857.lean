import Batteries

open Std

def listifyList (list1 : List String) : List (List String) :=
  list1.map (fun s => s.data.map (fun c => String.singleton c))

#guard listifyList ["Red", "Blue", "Black", "White", "Pink"] == [["R", "e", "d"], ["B", "l", "u", "e"], ["B", "l", "a", "c", "k"], ["W", "h", "i", "t", "e"], ["P", "i", "n", "k"]]
#guard listifyList ["python"] == [["p", "y", "t", "h", "o", "n"]]
#guard listifyList [" red ", "green", " black", "blue ", " orange", "brown"] == [[" ", "r", "e", "d", " "], ["g", "r", "e", "e", "n"], [" ", "b", "l", "a", "c", "k"], ["b", "l", "u", "e", " "], [" ", "o", "r", "a", "n", "g", "e"], ["b", "r", "o", "w", "n"]]
