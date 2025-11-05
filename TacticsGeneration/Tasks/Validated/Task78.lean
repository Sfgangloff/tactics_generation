import Batteries
open Std

def countSetBits (n : Nat) : Nat :=
  Id.run do
    let mut count := 0
    let mut x := n
    while x > 0 do
      count := count + (x % 2)
      x := x / 2
    return count

def countWithOddSetBits (n : Nat) : Nat :=
  let halfN := n / 2
  if n % 2 != 0 then
    (n + 1) / 2
  else
    let count := countSetBits n
    let ans := halfN
    if count % 2 != 0 then
      ans + 1
    else
      ans

#guard countWithOddSetBits 5 == 3
#guard countWithOddSetBits 10 == 5
#guard countWithOddSetBits 15 == 8
