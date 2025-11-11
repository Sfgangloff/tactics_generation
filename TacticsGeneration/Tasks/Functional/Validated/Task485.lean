import Batteries

open Std

def removeFirst (xs : List Int) (x : Int) : List Int :=
  match xs with
  | [] => []
  | y :: ys => if y == x then ys else y :: removeFirst ys x

def findMin (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | y :: ys => ys.foldl (fun m z => if z < m then z else m) y

def selectionSortAsc (xs : List Int) : List Int := Id.run do
  let mut rest := xs
  let mut res : List Int := []
  while !rest.isEmpty do
    let m := findMin rest
    let rest' := removeFirst rest m
    res := res ++ [m]
    rest := rest'
  return res

def is_palindrome (n : Int) : Bool := Id.run do
  if n < 0 then return false
  let nNat : Nat := Int.toNat n
  let mut divisor : Nat := 1
  while nNat / divisor >= 10 do
    divisor := divisor * 10
  let mut m := nNat
  let mut d := divisor
  while m != 0 do
    let leading := m / d
    let trailing := m % 10
    if !(leading == trailing) then return false
    m := (m % d) / 10
    d := d / 100
  return true

def largest_palindrome (A : List Int) (n : Nat) : Int := Id.run do
  let sorted := selectionSortAsc A
  let mut i := n
  while i > 0 do
    let idx := i - 1
    let x := sorted.getD idx 0
    if is_palindrome x then return x
    i := i - 1
  return -1

#guard largest_palindrome [1, 232, 54545, 999991] 4 == 54545
#guard largest_palindrome [1, 2, 3, 4, 5, 50] 6 == 5
#guard largest_palindrome [1, 3, 7, 9, 45] 5 == 9
