import Batteries

open Std

def lastElem {α : Type} [Inhabited α] : List α → α
| [] => default
| [a] => a
| _ :: xs => lastElem xs

def Extract {α : Type} [Inhabited α] (lst : List (List α)) : List α :=
  lst.map lastElem

#guard Extract [[1, 2, 3], [4, 5], [6, 7, 8, 9]] == [3, 5, 9]
#guard Extract [["x", "y", "z"], ["m"], ["a", "b"], ["u", "v"]] == ["z", "m", "b", "v"]
#guard Extract [[1, 2, 3], [4, 5]] == [3, 5]
