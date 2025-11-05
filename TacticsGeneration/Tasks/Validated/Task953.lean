import Batteries

open Std

def subset (ar : List Nat) (n : Nat) : Nat := Id.run do
  let mut res := 0
  if ar.isEmpty then
    return 0
  let mut mn := ar.head!
  for x in ar.drop 1 do
    if x < mn then
      mn := x
  let mut count := 0
  for x in ar do
    if x == mn then
      count := count + 1
  if count > res then
    res := count
  return res

#guard subset [1, 2, 3, 4] 4 = 1
#guard subset [5, 6, 9, 3, 4, 3, 4] 7 = 2
#guard subset [1, 2, 3] 3 = 1
