import Batteries
open Std

def modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y (fun row => row.modify x f)

def set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def generateMatrix (n : Nat) : List (List Nat) := Id.run do
  if n == 0 then
    return []
  let mut matrix : Array (Array Nat) := Array.replicate n (Array.replicate n 0)
  let mut rowSt : Int := 0
  let mut rowEd : Int := (Int.ofNat n) - 1
  let mut colSt : Int := 0
  let mut colEd : Int := (Int.ofNat n) - 1
  let mut current : Nat := 1
  let n2 := n * n
  while true do
    if current > n2 then break
    
    let mut c : Int := colSt
    while c ≤ colEd do
      matrix := matrix.set2d? rowSt.toNat c.toNat current
      current := current + 1
      c := c + 1
    rowSt := rowSt + 1
    
    let mut r : Int := rowSt
    while r ≤ rowEd do
      matrix := matrix.set2d? r.toNat colEd.toNat current
      current := current + 1
      r := r + 1
    colEd := colEd - 1
    
    let mut c2 : Int := colEd
    while c2 ≥ colSt do
      matrix := matrix.set2d? rowEd.toNat c2.toNat current
      current := current + 1
      c2 := c2 - 1
    rowEd := rowEd - 1
    
    let mut r2 : Int := rowEd
    while r2 ≥ rowSt do
      matrix := matrix.set2d? r2.toNat colSt.toNat current
      current := current + 1
      r2 := r2 - 1
    colSt := colSt + 1
  return matrix.toList.map (·.toList)

#guard generateMatrix 3 == [[1, 2, 3], [8, 9, 4], [7, 6, 5]]
#guard generateMatrix 2 == [[1, 2], [4, 3]]
#guard generateMatrix 7 == [[1, 2, 3, 4, 5, 6, 7], [24, 25, 26, 27, 28, 29, 8], [23, 40, 41, 42, 43, 30, 9], [22, 39, 48, 49, 44, 31, 10], [21, 38, 47, 46, 45, 32, 11], [20, 37, 36, 35, 34, 33, 12], [19, 18, 17, 16, 15, 14, 13]]
