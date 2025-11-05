import Batteries

open Std

def Sum_of_Inverse_Divisors (N Sum : Nat) : Float :=
  
  let numerator := Sum * 100
  let rounded := (numerator + N / 2) / N
  (Float.ofNat rounded) / 100.0

#guard Sum_of_Inverse_Divisors 6 12 == (2.0 : Float)
#guard Sum_of_Inverse_Divisors 9 13 == (1.44 : Float)
#guard Sum_of_Inverse_Divisors 1 4 == (4.0 : Float)
