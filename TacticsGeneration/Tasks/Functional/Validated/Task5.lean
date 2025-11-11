import Batteries

open Std

def countWays (n : Nat) : Nat := Id.run do
  let mut A := Array.replicate (n+1) 0
  let mut B := Array.replicate (n+1) 0
  A := A.modify 0 (fun _ => 1)
  A := A.modify 1 (fun _ => 0)
  B := B.modify 0 (fun _ => 0)
  B := B.modify 1 (fun _ => 1)
  for i in [2 : n+1] do
    A := A.set! i <| A[i-2]! + 2*B[i-1]!
    B := B.set! i <| A[i-1]! + B[i-2]!
  return A[n]!

#guard countWays 2 == 3
#guard countWays 8 == 153
#guard countWays 12 == 2131
