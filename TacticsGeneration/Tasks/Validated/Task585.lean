import Batteries

open Std

structure Item where
  name : String
  price : Float
  deriving BEq, Repr

def expensiveItems (items : List Item) (n : Nat) : List Item := Id.run do
  let rec findMax (ys : List Item) (i : Nat) (best? : Option (Item × Nat)) : Option (Item × Nat) :=
    match ys with
    | [] => best?
    | y :: ys' =>
      let best? :=
        match best? with
        | none => some (y, i)
        | some (b, j) => if y.price > b.price then some (y, i) else some (b, j)
      findMax ys' (i+1) best?
  let rec removeIdx (ys : List Item) (i : Nat) : List Item :=
    match ys with
    | [] => []
    | y :: ys' =>
      match i with
      | 0 => ys'
      | Nat.succ j => y :: removeIdx ys' j
  let mut xs := items
  let mut res : List Item := []
  for _ in [: n] do
    match findMax xs 0 none with
    | none => break
    | some (m, idx) =>
      res := res ++ [m]
      xs := removeIdx xs idx
  return res

#guard expensiveItems [{ name := "Item-1", price := (101.1 : Float) }, { name := "Item-2", price := (555.22 : Float) }] 1 == [{ name := "Item-2", price := (555.22 : Float) }]
#guard expensiveItems [{ name := "Item-1", price := (101.1 : Float) }, { name := "Item-2", price := (555.22 : Float) }, { name := "Item-3", price := (45.09 : Float) }] 2 == [{ name := "Item-2", price := (555.22 : Float) }, { name := "Item-1", price := (101.1 : Float) }]
#guard expensiveItems [{ name := "Item-1", price := (101.1 : Float) }, { name := "Item-2", price := (555.22 : Float) }, { name := "Item-3", price := (45.09 : Float) }, { name := "Item-4", price := (22.75 : Float) }] 1 == [{ name := "Item-2", price := (555.22 : Float) }]
