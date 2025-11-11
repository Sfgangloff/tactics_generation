import Batteries

open Std

private def insertBy {α} (cmp : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if cmp x y then x :: y :: ys else y :: insertBy cmp x ys

private def isort {α} (cmp : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy cmp x (isort cmp xs)

def smartNumber (n : Nat) : Nat := Id.run do
  let MAX : Nat := 3000
  let mut primes : Array Int := Array.replicate MAX 0
  let mut result : Array Nat := #[]
  for i in [2 : MAX] do
    if primes[i]! == 0 then
      primes := primes.set! i 1
      let mut j := i * 2
      while j < MAX do
        primes := primes.set! j (primes[j]! - 1)
        if primes[j]! + 3 == 0 then
          result := result.push j
        j := j + i
  let sorted := isort (· ≤ ·) result.toList
  return sorted.getD (n - 1) 0

#guard smartNumber 1 == 30
#guard smartNumber 50 == 273
#guard smartNumber 1000 == 2664
