import Batteries

open Std

def sumDiv (number : Nat) : Nat := Id.run do
  let mut divisors : Array Nat := #[1]
  for i in [2 : number] do
    if number % i == 0 then
      divisors := divisors.push i
  return Array.foldl (fun acc x => acc + x) 0 divisors

#guard sumDiv 8 = 7
#guard sumDiv 12 = 16
#guard sumDiv 7 = 1
