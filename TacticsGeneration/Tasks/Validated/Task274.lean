import Batteries

open Std

def even_binomial_Coeff_Sum (n : Nat) : Nat :=
  1 <<< (n - 1)

#guard even_binomial_Coeff_Sum 4 = 8
#guard even_binomial_Coeff_Sum 6 = 32
#guard even_binomial_Coeff_Sum 2 = 2
