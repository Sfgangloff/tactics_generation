import Batteries

open Std

def odd_Days (N : Nat) : Nat :=
  let hund1 := N / 100
  let hund4 := N / 400
  let leap := N >>> 2
  let ordd0 := N - leap
  let (ordd1, leap1) :=
    if hund1 == 0 then
      (ordd0, leap)
    else
      (ordd0 + hund1, leap - hund1)
  let (ordd2, leap2) :=
    if hund4 == 0 then
      (ordd1, leap1)
    else
      (ordd1 - hund4, leap1 + hund4)
  let days := ordd2 + leap2 * 2
  days % 7

#guard odd_Days 100 = 5
#guard odd_Days 50 = 6
#guard odd_Days 75 = 2
