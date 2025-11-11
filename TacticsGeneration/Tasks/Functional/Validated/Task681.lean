import Batteries

open Std

def smallestDivisor (n : Nat) : Nat := Id.run do
  if n % 2 == 0 then
    return 2
  let limit := Nat.sqrt n
  for i in [3 : limit + 1] do
    if (i % 2 == 1) && (n % i == 0) then return i
  return n

#guard smallestDivisor 10 = 2
#guard smallestDivisor 25 = 5
#guard smallestDivisor 31 = 31
