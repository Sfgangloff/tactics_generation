import Batteries

open Std

def hasAsciiLower (s : String) : Bool :=
  s.data.any (fun c => 'a' ≤ c && c ≤ 'z')

def hasAsciiUpper (s : String) : Bool :=
  s.data.any (fun c => 'A' ≤ c && c ≤ 'Z')

def hasDigit (s : String) : Bool :=
  s.data.any (fun c => '0' ≤ c && c ≤ '9')

def hasSpecial (s : String) : Bool :=
  s.data.any (fun c => c = '$' || c = '#' || c = '@')

def hasWhitespace (s : String) : Bool :=
  s.data.any (fun c => c.isWhitespace)

def pass_validity (p : String) : Bool :=
  if p.length < 6 || p.length > 12 then
    false
  else if !hasAsciiLower p then
    false
  else if !hasDigit p then
    false
  else if !hasAsciiUpper p then
    false
  else if !hasSpecial p then
    false
  else if hasWhitespace p then
    false
  else
    true

#guard pass_validity "password" = false
#guard pass_validity "Password@10" = true
#guard pass_validity "password@10" = false
