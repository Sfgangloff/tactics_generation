import Batteries

open Std

def sumSeries : Nat → Nat
| 0 => 0
| 1 => 1
| Nat.succ (Nat.succ k) => (k + 2) + sumSeries k

#guard sumSeries 6 = 12
#guard sumSeries 10 = 30
#guard sumSeries 9 = 25
