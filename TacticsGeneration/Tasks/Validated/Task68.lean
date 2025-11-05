import Batteries

open Std

def isMonotonic (A : List Int) : Bool :=
  (A.length ≤ 1) ||
  ((A.foldl (fun (result, prev) x => (result && prev <= x, x)) (true, A.head!)).1 ||
   (A.foldl (fun (result, prev) x => (result && prev >= x, x)) (true, A.head!)).1)

#guard isMonotonic [6, 5, 4, 4] == true
#guard isMonotonic [1, 2, 2, 3] == true
#guard isMonotonic [1, 3, 2] == false
