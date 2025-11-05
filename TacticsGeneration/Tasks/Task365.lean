import Batteries
open Std

private def countDigitAux (n count : Nat) : Nat :=
  if h : n ≠ 0 then
    countDigitAux (n / 10) (count + 1)
  else
    count
termination_by n count => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 10)

def countDigit (n : Nat) : Nat :=
  countDigitAux n 0

#guard countDigit 12345 = 5
#guard countDigit 11223305 = 8
#guard countDigit 4123459 = 7
