import Batteries

open Std

structure Item where
  name : String
  price : Float
deriving Repr, BEq

private def findMinByPrice (l : List Item) : Option Item :=
  match l with
  | [] => none
  | h :: t =>
    some <| t.foldl (fun m x => if x.price < m.price then x else m) h

private def removeFirst (l : List Item) (x : Item) : List Item :=
  match l with
  | [] => []
  | h :: t => if h == x then t else h :: removeFirst t x

def cheapItems (items : List Item) (n : Nat) : List Item := Id.run do
  let mut rest := items
  let mut res : List Item := []
  for _ in [: n] do
    match findMinByPrice rest with
    | none => break
    | some m =>
      res := res ++ [m]
      rest := removeFirst rest m
  return res

#guard cheapItems [{ name := "Item-1", price := 101.1 }, { name := "Item-2", price := 555.22 }] 1 == [{ name := "Item-1", price := 101.1 }]
#guard cheapItems [{ name := "Item-1", price := 101.1 }, { name := "Item-2", price := 555.22 }] 2 == [{ name := "Item-1", price := 101.1 }, { name := "Item-2", price := 555.22 }]
#guard cheapItems [
  { name := "Item-1", price := 101.1 },
  { name := "Item-2", price := 555.22 },
  { name := "Item-3", price := 45.09 },
  { name := "Item-4", price := 22.75 }
] 1 == [{ name := "Item-4", price := 22.75 }]
