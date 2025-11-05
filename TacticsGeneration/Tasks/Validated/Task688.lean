import Batteries

open Std

def lenComplex (a b : Int) : Float :=
  let af := Float.ofInt a
  let bf := Float.ofInt b
  Float.sqrt (af * af + bf * bf)

#guard lenComplex 3 4 == 5.0
#guard lenComplex 9 10 == 13.45362404707371
#guard lenComplex 7 9 == 11.40175425099138
