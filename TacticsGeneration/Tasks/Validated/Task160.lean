import Batteries

open Std

def solution (a b n : Nat) : Sum (String × Nat × String × Nat) String := Id.run do
  for i in [: n+1] do
    if Nat.ble (i * a) n then
      if (n - i * a) % b == 0 then
        let y := (n - i * a) / b
        return Sum.inl ("x = ", i, ", y = ", y)
      else
        pure ()
    else
      pure ()
  return Sum.inr "No solution"

#guard solution 2 3 7 = Sum.inl ("x = ", 2, ", y = ", 1)
#guard solution 4 2 7 = Sum.inr "No solution"
#guard solution 1 13 17 = Sum.inl ("x = ", 4, ", y = ", 1)
