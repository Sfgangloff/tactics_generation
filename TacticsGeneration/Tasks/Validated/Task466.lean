import Batteries

open Std

private def getAt (arr : List Nat) (i : Nat) : Nat := arr.getD i 0

def findPeakUtil (arr : List Nat) (low high n : Nat) : Nat :=
  let rec go (low high fuel : Nat) : Nat :=
    let mid := low + (high - low) / 2
    
    if hLeft : mid = 0 ∨ getAt arr (mid - 1) ≤ getAt arr mid then
      if hRight : mid = n - 1 ∨ getAt arr (mid + 1) ≤ getAt arr mid then
        mid
      else
        if fuel = 0 then mid else go (mid + 1) high (fuel - 1)
    else
      if fuel = 0 then mid else go low (mid - 1) (fuel - 1)
  
  go low high (high - low + 2)

def findPeak (arr : List Nat) (n : Nat) : Nat :=
  findPeakUtil arr 0 (n - 1) n

#guard findPeak [1, 3, 20, 4, 1, 0] 6 == 2
#guard findPeak [2, 3, 4, 5, 6] 5 == 4
#guard findPeak [8, 9, 11, 12, 14, 15] 6 == 5
