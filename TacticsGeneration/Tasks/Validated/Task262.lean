import Batteries

open Std

def splitTwoParts {α : Type} (list1 : List α) (L : Nat) : (List α × List α) :=
  (list1.take L, list1.drop L)

#guard splitTwoParts [1, 1, 2, 3, 4, 4, 5, 1] 3 = ([1, 1, 2], [3, 4, 4, 5, 1])
#guard splitTwoParts ["a", "b", "c", "d"] 2 = (["a", "b"], ["c", "d"])
#guard splitTwoParts ["p", "y", "t", "h", "o", "n"] 4 = (["p", "y", "t", "h"], ["o", "n"])
