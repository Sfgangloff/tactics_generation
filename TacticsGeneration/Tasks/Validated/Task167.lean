import Batteries

open Std

def next_Power_Of_2 (n : Nat) : Nat := Id.run do
  let mut count := 0
  if n != 0 && (n &&& (n - 1)) == 0 then
    return n
  let mut m := n
  while m != 0 do
    m := m >>> 1
    count := count + 1
  return (1 <<< count)

#guard next_Power_Of_2 0 = 1
#guard next_Power_Of_2 5 = 8
#guard next_Power_Of_2 17 = 32
