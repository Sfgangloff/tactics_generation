import Batteries

open Std

def averageTuple (nums : List (List Int)) : List Float := Id.run do
  if nums.isEmpty then
    return []
  let cols := nums.head!.length
  let rows := nums.length
  let mut res : Array Float := #[]
  for j in [0:cols] do
    let mut s : Float := 0.0
    for row in nums do
      s := s + Float.ofInt (row.getD j 0)
    res := res.push (s / Float.ofNat rows)
  return res.toList

#guard averageTuple [[10, 10, 10, 12], [30, 45, 56, 45], [81, 80, 39, 32], [1, 2, 3, 4]] == [30.5, 34.25, 27.0, 23.25]
#guard averageTuple [[1, 1, -5], [30, -15, 56], [81, -60, -39], [-10, 2, 3]] == [25.5, -18.0, 3.75]
#guard averageTuple [[100, 100, 100, 120], [300, 450, 560, 450], [810, 800, 390, 320], [10, 20, 30, 40]] == [305.0, 342.5, 270.0, 232.5]
