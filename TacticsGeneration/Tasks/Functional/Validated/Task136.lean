import Batteries

open Std

def calElectbill (units : Nat) : Float :=
  let amountCents :=
    if units < 50 then
      units * 260
    else if units <= 100 then
      13000 + (units - 50) * 325
    else if units <= 200 then
      13000 + 16250 + (units - 100) * 526
    else
      13000 + 16250 + 52600 + (units - 200) * 845
  let surchargeCents :=
    if units < 50 then 2500
    else if units <= 100 then 3500
    else if units <= 200 then 4500
    else 7500
  let totalCents := amountCents + surchargeCents
  (Float.ofNat totalCents) / 100.0

#guard calElectbill 75 == 246.25
#guard calElectbill 265 == 1442.75
#guard calElectbill 100 == 327.5
