import Batteries

open Std

def dropLeadingZeros (s : String) : String :=
  String.mk (s.data.dropWhile (fun c => c == '0'))

def removezero_ip (ip : String) : String :=
  let parts := ip.splitOn "."
  let parts2 := parts.map dropLeadingZeros
  match parts2 with
  | [] => ""
  | p::ps => ps.foldl (fun acc s => acc ++ "." ++ s) p

#guard removezero_ip "216.08.094.196" = "216.8.94.196"
#guard removezero_ip "12.01.024" = "12.1.24"
#guard removezero_ip "216.08.094.0196" = "216.8.94.196"
