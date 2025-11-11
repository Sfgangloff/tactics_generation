import Batteries

open Std

def findAverageOfCube (n : Nat) : Float := Id.run do
  
  let mut s : Nat := 0
  for i in [1 : n+1] do
    s := s + i * i * i
  let avg := (Float.ofNat s) / (Float.ofNat n)
  
  return avg

#guard findAverageOfCube 2 == 4.5
#guard findAverageOfCube 3 == 12.0
#guard findAverageOfCube 1 == 1.0
