import Batteries

open Std

def check_IP (Ip : String) : String :=
  let parts := Ip.splitOn "."
  if parts.length != 4 then
    "Invalid IP address"
  else
    if parts.all (fun p =>
      match p.toNat? with
      | some n => n ≤ 255
      | none => false) then
      "Valid IP address"
    else
      "Invalid IP address"

#guard check_IP "192.168.0.1" == "Valid IP address"
#guard check_IP "110.234.52.124" == "Valid IP address"
#guard check_IP "366.1.2.2" == "Invalid IP address"
