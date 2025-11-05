import Batteries

open Std

def calSum (n : Nat) : Nat := Id.run do
  let mut a := 3
  let mut b := 0
  let mut c := 2
  if n == 0 then
    return 3
  if n == 1 then
    return 3
  if n == 2 then
    return 5
  let mut s := 5
  let mut m := n
  while m > 2 do
    let d := a + b
    s := s + d
    a := b
    b := c
    c := d
    m := m - 1
  return s

#guard calSum 9 = 49
#guard calSum 10 = 66
#guard calSum 11 = 88
