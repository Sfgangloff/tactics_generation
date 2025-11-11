import Batteries

open Std

def binomial_Coeff (n k : Nat) : Nat :=
  match n with
  | 0 => if k == 0 then 1 else 0
  | Nat.succ n' =>
    if k > Nat.succ n' then 0
    else if k == 0 || k == Nat.succ n' then 1
    else binomial_Coeff n' (k - 1) + binomial_Coeff n' k

#guard binomial_Coeff 5 2 = 10
#guard binomial_Coeff 4 3 = 4
#guard binomial_Coeff 3 2 = 3
#guard binomial_Coeff 14 6 = 3003
