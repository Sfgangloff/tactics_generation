import Batteries

open Std

def perimeterPolygon (s l : Nat) : Nat :=
  let perimeter := s * l
  perimeter

#guard perimeterPolygon 4 20 = 80
#guard perimeterPolygon 10 15 = 150
#guard perimeterPolygon 9 7 = 63
