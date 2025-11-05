import Batteries

open Std

def find_Parity (x : Nat) : String :=
  let y0 := x ^^^ (x >>> 1)
  let y1 := y0 ^^^ (y0 >>> 2)
  let y2 := y1 ^^^ (y1 >>> 4)
  let y3 := y2 ^^^ (y2 >>> 8)
  let y4 := y3 ^^^ (y3 >>> 16)
  if (y4 &&& 1) == 1 then "Odd Parity" else "Even Parity"

#guard find_Parity 12 = "Even Parity"
#guard find_Parity 7 = "Odd Parity"
#guard find_Parity 10 = "Even Parity"
