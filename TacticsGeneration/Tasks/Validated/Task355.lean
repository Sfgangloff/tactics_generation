import Batteries

open Std

def countRectangles (radius : Nat) : Nat := Id.run do
  let mut rectangles := 0
  let diameter := 2 * radius
  let diameterSquare := diameter * diameter
  for a in [1 : 2 * radius] do
    for b in [1 : 2 * radius] do
      let diagnalLengthSquare := a * a + b * b
      if diagnalLengthSquare <= diameterSquare then
        rectangles := rectangles + 1
  return rectangles

#guard countRectangles 2 = 8
#guard countRectangles 1 = 1
#guard countRectangles 0 = 0
