import Batteries
open Std

/-!
  Auto-generated from task 12.
  Module: Task12
-/


namespace Task12

-- Sum of a row (array of Ints)
def rowSum (row : Array Int) : Int := Id.run do
  let mut s : Int := 0
  for x in row do
    s := s + x
  return s

-- Sort matrix rows by ascending sum of their elements
-- Preconditions: none (works for empty matrix and empty rows)
def sortMatrix (M : Array (Array Int)) : Array (Array Int) := Id.run do
  let mut arr := M
  -- Selection sort by row sum
  for i in [:arr.size] do
    let mut minIdx := i
    let mut minSum := rowSum (arr[i]!)
    for j in [i+1:arr.size] do
      let s := rowSum (arr[j]!)
      if s < minSum then
        minSum := s
        minIdx := j
    if minIdx != i then
      let tmp := arr[i]!
      let vmin := arr[minIdx]!
      arr := arr.set! i vmin
      arr := arr.set! minIdx tmp
  return arr

end Task12


-- Tests

namespace Task12

#eval
  let m1 : Array (Array Int) := #[(#[(1 : Int), 2, 3]), (#[(2 : Int), 4, 5]), (#[(1 : Int), 1, 1])]
  let e1 : Array (Array Int) := #[(#[(1 : Int), 1, 1]), (#[(1 : Int), 2, 3]), (#[(2 : Int), 4, 5])]
  let m2 : Array (Array Int) := #[(#[(1 : Int), 2, 3]), (#[(-2 : Int), 4, -5]), (#[(1 : Int), -1, 1])]
  let e2 : Array (Array Int) := #[(#[(-2 : Int), 4, -5]), (#[(1 : Int), -1, 1]), (#[(1 : Int), 2, 3])]
  let m3 : Array (Array Int) := #[(#[(5 : Int), 8, 9]), (#[(6 : Int), 4, 3]), (#[(2 : Int), 1, 4])]
  let e3 : Array (Array Int) := #[(#[(2 : Int), 1, 4]), (#[(6 : Int), 4, 3]), (#[(5 : Int), 8, 9])]
  let ok1 := (sortMatrix m1) == e1
  let ok2 := (sortMatrix m2) == e2
  let ok3 := (sortMatrix m3) == e3
  ok1 && ok2 && ok3

end Task12