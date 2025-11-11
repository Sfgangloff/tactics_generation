import Batteries

open Std

def roundNum (n m : Nat) : Nat :=
  
  let a := (n / m) * m
  let b := a + m
  if n - a > b - n then b else a

#guard roundNum 4722 10 = 4720
#guard roundNum 1111 5 = 1110
#guard roundNum 219 2 = 218
