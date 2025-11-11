import Batteries

open Std

def divisibleByDigits (startnum endnum : Nat) : List Nat := Id.run do
  let mut res : Array Nat := #[]
  for n in [startnum : endnum + 1] do
    let s := toString n
    let chars := s.data
    let ok := chars.foldl (init := true) (fun acc c =>
      if acc then
        let d := c.toNat - '0'.toNat
        if d == 0 then false else n % d == 0
      else
        false)
    if ok then
      res := res.push n
  return res.toList

#guard divisibleByDigits 1 22 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 15, 22]
#guard divisibleByDigits 1 15 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 15]
#guard divisibleByDigits 20 25 == [22, 24]
