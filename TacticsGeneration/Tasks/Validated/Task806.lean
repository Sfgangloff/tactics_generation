import Batteries

open Std

def isUpperAscii (c : Char) : Bool :=
  ('A' ≤ c) && (c ≤ 'Z')

def max_run_uppercase (test_str : String) : Nat := Id.run do
  let mut cnt := 0
  let mut res := 0
  let mut lastIsUpper := false
  for c in test_str.toList do
    if isUpperAscii c then
      cnt := cnt + 1
      lastIsUpper := true
    else
      res := cnt
      cnt := 0
      lastIsUpper := false
  if lastIsUpper then
    res := cnt
  return res

#guard max_run_uppercase "GeMKSForGERksISBESt" == 5
#guard max_run_uppercase "PrECIOusMOVemENTSYT" == 6
#guard max_run_uppercase "GooGLEFluTTER" == 4
