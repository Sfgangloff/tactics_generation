import Batteries
open Std

def babylonianSquareroot (number : Float) : Float :=
  if number == 0.0 then
    0.0
  else
    let rec loop (g g2 : Float) (fuel : Nat) : Float :=
      if g == g2 then
        g
      else
        match fuel with
        | 0 => g
        | Nat.succ fuel' =>
          let n := number / g
          let g2' := g
          let g' := (g + n) / 2.0
          loop g' g2' fuel'
    loop (number / 2.0) ((number / 2.0) + 1.0) 10000

#guard babylonianSquareroot 10 == 3.162277660168379
#guard babylonianSquareroot 2 == 1.414213562373095
#guard babylonianSquareroot 9 == 3.0
