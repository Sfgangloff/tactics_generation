import Batteries

open Std

def maxVolume (s : Nat) : Nat := Id.run do
  let mut maxvalue := 0
  
  for i in [0 : s - 1] do
    
    for j in [0 : s] do
      let k := s - i - j
      let prod := i * j * k
      if prod > maxvalue then
        maxvalue := prod
  return maxvalue

#guard maxVolume 8 = 18
#guard maxVolume 4 = 2
#guard maxVolume 1 = 0
