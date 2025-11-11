import Batteries

open Std

def nthSuperUglyNumber (n : Nat) (primes : List Nat) : Nat := Id.run do
  
  
  let k := primes.length
  let primesArr := primes.toArray
  let mut idx : Array Nat := Array.replicate k 0
  let mut uglies : Array Nat := #[1]
  
  for _ in [1 : n] do
    
    let mut minVal := primesArr[0]! * uglies[idx[0]!]!
    for j in [1 : k] do
      let p := primesArr[j]!
      let i := idx[j]!
      let u := uglies[i]!
      let cand := p * u
      if cand < minVal then
        minVal := cand
    
    let last := uglies[uglies.size - 1]!
    if minVal != last then
      uglies := uglies.push minVal
    
    for j in [0 : k] do
      let p := primesArr[j]!
      let i := idx[j]!
      let u := uglies[i]!
      if p * u == minVal then
        idx := idx.set! j (i + 1)
  return uglies[n - 1]!

#guard nthSuperUglyNumber 12 [2, 7, 13, 19] = 32
#guard nthSuperUglyNumber 10 [2, 7, 13, 19] = 26
#guard nthSuperUglyNumber 100 [2, 7, 13, 19] = 5408
