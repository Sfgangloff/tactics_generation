import Batteries

open Std

def maxSimilarIndices (test_list1 test_list2 : List (Nat × Nat)) : List (Nat × Nat) :=
  List.zipWith (fun x y => (Nat.max x.fst y.fst, Nat.max x.snd y.snd)) test_list1 test_list2

#guard maxSimilarIndices [(2, 4), (6, 7), (5, 1)] [(5, 4), (8, 10), (8, 14)] = [(5, 4), (8, 10), (8, 14)]
#guard maxSimilarIndices [(3, 5), (7, 8), (6, 2)] [(6, 5), (9, 11), (9, 15)] = [(6, 5), (9, 11), (9, 15)]
#guard maxSimilarIndices [(4, 6), (8, 9), (7, 3)] [(7, 6), (10, 12), (10, 16)] = [(7, 6), (10, 12), (10, 16)]
