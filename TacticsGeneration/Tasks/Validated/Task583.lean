import Batteries

open Std

partial def catalanNumber (num : Nat) : Nat := Id.run do
  if num <= 1 then
    return 1
  let mut res := 0
  for i in [:num] do
    res := res + catalanNumber i * catalanNumber (num - i - 1)
  return res

#guard catalanNumber 10 == 16796
#guard catalanNumber 9 == 4862
#guard catalanNumber 7 == 429
