import Batteries

open Std

def No_of_Triangle (N K : Int) : Int :=
  if N < K then -1
  else
    let Tri_up := ((N - K + 1) * (N - K + 2)) / 2
    let Tri_down := ((N - 2 * K + 1) * (N - 2 * K + 2)) / 2
    Tri_up + Tri_down

#guard No_of_Triangle 4 2 = 7
#guard No_of_Triangle 4 3 = 3
#guard No_of_Triangle 1 3 = -1
