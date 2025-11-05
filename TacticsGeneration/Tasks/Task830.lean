import Batteries
open Std

def pow10 (d : Nat) : Float :=
  let rec loop (n : Nat) (acc : Float) : Float :=
    match n with
    | 0 => acc
    | Nat.succ n' => loop n' (acc * 10.0)
  loop d 1.0

def roundUp (a : Float) (digits : Nat) : Float :=
  let scale := pow10 digits
  let c := Float.ceil (a * scale)
  c / scale

#guard roundUp 123.01247 0 = 124.0
#guard roundUp 123.01247 1 = 123.1
#guard roundUp 123.01247 2 = 123.02
