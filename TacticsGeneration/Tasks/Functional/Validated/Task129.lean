import Batteries

open Std

def magicSquareTest (myMatrix : List (List Nat)) : Bool :=
  let iSize := (myMatrix.headD []).length
  let sumList := Id.run do
    let mut sums := ([] : List Nat)
    for lines in myMatrix do
      sums := sums ++ [lines.foldl (fun acc x => acc + x) 0]
    for col in [0:iSize] do
      sums := sums ++ [myMatrix.foldl (fun acc row => acc + row.getD col 0) 0]
    let result1 := List.foldl (fun acc i => acc + (myMatrix.getD i []).getD i 0) 0 (List.range iSize)
    sums := sums ++ [result1]
    let result2 := List.foldl (fun acc i => acc + (myMatrix.getD (iSize - i - 1) []).getD i 0) 0 (List.range iSize)
    sums := sums ++ [result2]
    return sums
  HashSet.ofList sumList |>.size == 1

#guard magicSquareTest [[7, 12, 1, 14], [2, 13, 8, 11], [16, 3, 10, 5], [9, 6, 15, 4]] = true
#guard magicSquareTest [[2, 7, 6], [9, 5, 1], [4, 3, 8]] = true
#guard magicSquareTest [[2, 7, 6], [9, 5, 1], [4, 3, 7]] = false
