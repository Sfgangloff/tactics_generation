import Batteries

open Std

def find_exponentio (test_tup1 test_tup2 : List Nat) : List Nat :=
  (List.zip test_tup1 test_tup2).map (fun (a, b) => a ^ b)

#guard find_exponentio [10, 4, 5, 6] [5, 6, 7, 5] == [100000, 4096, 78125, 7776]
#guard find_exponentio [11, 5, 6, 7] [6, 7, 8, 6] == [1771561, 78125, 1679616, 117649]
#guard find_exponentio [12, 6, 7, 8] [7, 8, 9, 7] == [35831808, 1679616, 40353607, 2097152]
