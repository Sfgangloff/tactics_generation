import Batteries

open Std

def multiplyList (items : List Int) : Int := Id.run do
  let mut tot : Int := 1
  for x in items do
    tot := tot * x
  return tot

#guard multiplyList [1, -2, 3] = -6
#guard multiplyList [1, 2, 3, 4] = 24
#guard multiplyList [3, 1, 2, 3] = 18
