import Batteries

open Std

def decreasingTrend (nums : List Int) : Bool :=
  let rec aux : List Int → Bool
    | [] => true
    | [_] => true
    | a :: b :: t =>
      if h : a <= b then
        aux (b :: t)
      else
        false
  aux nums

#guard decreasingTrend [-4, -3, -2, -1] == true
#guard decreasingTrend [1, 2, 3] == true
#guard decreasingTrend [3, 2, 1] == false
