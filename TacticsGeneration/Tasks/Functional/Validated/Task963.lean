import Batteries

open Std

def discriminantValue (x y z : Int) : String × Int :=
  let discriminant := y*y - 4*x*z
  if _h : discriminant > 0 then
    ("Two solutions", discriminant)
  else if _h2 : discriminant = 0 then
    ("one solution", discriminant)
  else
    ("no real solution", discriminant)

#guard discriminantValue 4 8 2 = ("Two solutions", 32)
#guard discriminantValue 5 7 9 = ("no real solution", -131)
#guard discriminantValue 0 0 9 = ("one solution", 0)
