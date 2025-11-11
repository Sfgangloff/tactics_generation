import Batteries

open Std

def swapCount (s : String) : Nat := Id.run do
  let chars := s.data
  let mut count_left : Int := 0
  let mut count_right : Int := 0
  let mut swap : Int := 0
  let mut imbalance : Int := 0
  for c in chars do
    if c == '[' then
      count_left := count_left + 1
      if imbalance > 0 then
        swap := swap + imbalance
        imbalance := imbalance - 1
    else if c == ']' then
      count_right := count_right + 1
      imbalance := count_right - count_left
    else
      pure ()
  return swap.toNat

#guard swapCount "[]][][" == 2
#guard swapCount "[[][]]" == 0
#guard swapCount "[[][]]][" == 1
