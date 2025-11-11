import Batteries

open Std

def rearExtract (test_list : List (Nat × String × Nat)) : List Nat :=
  test_list.map (fun (_, _, c) => c)

#guard rearExtract [(1, "Rash", 21), (2, "Varsha", 20), (3, "Kil", 19)] == [21, 20, 19]
#guard rearExtract [(1, "Sai", 36), (2, "Ayesha", 25), (3, "Salman", 45)] == [36, 25, 45]
#guard rearExtract [(1, "Sudeep", 14), (2, "Vandana", 36), (3, "Dawood", 56)] == [14, 36, 56]
