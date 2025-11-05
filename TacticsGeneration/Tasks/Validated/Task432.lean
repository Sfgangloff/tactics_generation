import Batteries

open Std

def medianTrapezium (base1 base2 height : Nat) : Float :=
  let median := 0.5 * Float.ofNat (base1 + base2)
  median

#guard medianTrapezium 15 25 35 == 20.0
#guard medianTrapezium 10 20 30 == 15.0
#guard medianTrapezium 6 9 4 == 7.5
