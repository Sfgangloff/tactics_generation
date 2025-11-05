import Batteries

open Std

def areaTrapezium (base1 base2 height : Nat) : Nat :=
  ((base1 + base2) * height) / 2

#guard areaTrapezium 6 9 4 = 30
#guard areaTrapezium 10 20 30 = 450
#guard areaTrapezium 15 25 35 = 700
