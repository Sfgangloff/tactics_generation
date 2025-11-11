import Batteries
open Std

inductive Item where
  | num : Nat → Item
  | tup : List Nat → Item
  deriving Repr, BEq

def countFirstElements (test_tup : List Item) : Nat := Id.run do
  let mut count := 0
  let mut i := 0
  for ele in test_tup do
    count := i
    match ele with
    | Item.tup _ => break
    | _ => ()
    i := i + 1
  return count

#guard countFirstElements [Item.num 1, Item.num 5, Item.num 7, Item.tup [4, 6], Item.num 10] = 3
#guard countFirstElements [Item.num 2, Item.num 9, Item.tup [5, 7], Item.num 11] = 2
#guard countFirstElements [Item.num 11, Item.num 15, Item.num 5, Item.num 8, Item.tup [2, 3], Item.num 8] = 4
