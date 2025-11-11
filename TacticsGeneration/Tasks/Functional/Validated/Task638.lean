import Batteries
open Std

def wind_chill (v t : Int) : Int :=
  let vF := Float.ofInt v
  let tF := Float.ofInt t
  let p := Float.pow vF 0.16
  let wc := 13.12 + 0.6215 * tF - 11.37 * p + 0.3965 * tF * p
  let r := Float.round wc
  Int64.toInt (Float.toInt64 r)

#guard wind_chill 120 35 = 40
#guard wind_chill 40 70 = 86
#guard wind_chill 10 100 = 116
