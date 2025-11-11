import Batteries
open Std

def maxProductTuple (list1 : List (Nat × Nat)) : Nat :=
  list1.foldl (fun acc (x, y) => Nat.max acc (x * y)) 0

#eval (maxProductTuple [(2, 7), (2, 6), (1, 8), (4, 9)] == 36)
#eval (maxProductTuple [(10, 20), (15, 2), (5, 10)] == 200)
#eval (maxProductTuple [(11, 44), (10, 15), (20, 5), (12, 9)] == 484)
