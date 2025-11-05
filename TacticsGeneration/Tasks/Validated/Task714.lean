import Batteries

open Std

def countFac (n : Nat) : Nat := Id.run do
  
  let m := n
  let mut count := 0
  let mut i := 2
  let mut n0 := n
  while h : i * i ≤ m do
    let mut total := 0
    while n0 % i == 0 do
      n0 := n0 / i
      total := total + 1
    let mut temp := 0
    let mut j := 1
    while h2 : temp + j ≤ total do
      temp := temp + j
      count := count + 1
      j := j + 1
    i := i + 1
  if n0 != 1 then
    count := count + 1
  return count

#guard countFac 24 == 3
#guard countFac 12 == 2
#guard countFac 4 == 1
