import Batteries
open Std

structure Pair where
  a : Nat
  b : Nat
deriving Inhabited

def maxChainLength (arr : List Pair) (n : Nat) : Nat := Id.run do
  
  let arrA := arr.toArray
  let mut mcl : Array Nat := Array.replicate n 1
  for i in [1 : n] do
    for j in [0 : i] do
      if arrA[i]!.a > arrA[j]!.b && mcl[i]! < mcl[j]! + 1 then
        mcl := mcl.set! i (mcl[j]! + 1)
  let mut mx := 0
  for i in [0 : n] do
    if mx < mcl[i]! then
      mx := mcl[i]!
  return mx

#guard maxChainLength [Pair.mk 5 24, Pair.mk 15 25, Pair.mk 27 40, Pair.mk 50 60] 4 = 3
#guard maxChainLength [Pair.mk 1 2, Pair.mk 3 4, Pair.mk 5 6, Pair.mk 7 8] 4 = 4
#guard maxChainLength [Pair.mk 19 10, Pair.mk 11 12, Pair.mk 13 14, Pair.mk 15 16, Pair.mk 31 54] 5 = 5
