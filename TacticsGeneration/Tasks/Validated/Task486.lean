import Batteries
open Std

def powFloat (x : Float) (k : Nat) : Float := Id.run do
  let mut res := 1.0
  for _ in [:k] do
    res := res * x
  return res

def nCr (n r : Nat) : Float := Id.run do
  let mut r2 := r
  if Float.ofNat r > Float.ofNat n / 2.0 then
    r2 := n - r
  let mut answer : Float := 1.0
  for i in [1 : r2 + 1] do
    let num := Float.ofNat (n - r2 + i)
    let den := Float.ofNat i
    answer := answer * num
    answer := answer / den
  return answer

def binomialProbability (n k : Nat) (p : Float) : Float :=
  nCr n k * powFloat p k * powFloat (1.0 - p) (n - k)

macro "#guard " t:term : command =>
  `( #eval (if $t then () else (panic! "guard failed" : Unit)) )

#guard (binomialProbability 10 5 (1.0/3.0) == 0.13656454808718185)
#guard (binomialProbability 11 6 (2.0/4.0) == 0.2255859375)
#guard (binomialProbability 12 7 (3.0/5.0) == 0.227030335488)
