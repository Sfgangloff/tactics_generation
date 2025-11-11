import Batteries

open Std

def gcd (x y : Nat) : Nat := Id.run do
  let mut g := 1
  if x % y == 0 then
    return y
  let half := y / 2
  for i in [1 : half + 1] do
    let k := half - (i - 1)
    if x % k == 0 && y % k == 0 then
      g := k
      return g
  return g

#guard gcd 12 17 = 1
#guard gcd 4 6 = 2
#guard gcd 2 9 = 1
