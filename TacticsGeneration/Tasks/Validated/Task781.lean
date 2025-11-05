import Batteries

open Std

def count_Divisors (n : Nat) : String := Id.run do
  let mut count := 0
  for i in [1 : Nat.sqrt n + 2] do
    if n % i == 0 then
      if n / i == i then
        count := count + 1
      else
        count := count + 2
  if count % 2 == 0 then
    return "Even"
  else
    return "Odd"

#guard count_Divisors 10 == "Even"
#guard count_Divisors 100 == "Odd"
#guard count_Divisors 125 == "Even"
