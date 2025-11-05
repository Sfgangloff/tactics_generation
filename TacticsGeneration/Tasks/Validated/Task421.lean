import Batteries

open Std

def concatenateTuple (test_tup : List String) : String :=
  let delim := "-"
  let res := (test_tup.map (fun ele => toString ele ++ delim)).foldl (· ++ ·) ""
  let res := res.take (res.length - delim.length)
  toString res

#guard concatenateTuple ["ID", "is", "4", "UTS"] = "ID-is-4-UTS"
#guard concatenateTuple ["QWE", "is", "4", "RTY"] = "QWE-is-4-RTY"
#guard concatenateTuple ["ZEN", "is", "4", "OP"] = "ZEN-is-4-OP"
