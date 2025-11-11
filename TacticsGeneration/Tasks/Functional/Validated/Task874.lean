import Batteries

open Std

def check_Concat (str1 str2 : String) : Bool := Id.run do
  let N := str1.length
  let M := str2.length
  if N % M != 0 then
    return false
  for i in [0 : N] do
    let c1 := (str1.drop i).take 1
    let c2 := (str2.drop (i % M)).take 1
    if c1 != c2 then return false
  return true

#guard check_Concat "abcabcabc" "abc" == true
#guard check_Concat "abcab" "abc" == false
#guard check_Concat "aba" "ab" == false
