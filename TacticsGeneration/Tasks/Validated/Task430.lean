import Batteries

open Std

def parabolaDirectrix (a b c : Int) : Int :=
  let directrix := c - ((b * b) + 1) * 4 * a
  directrix

#guard parabolaDirectrix 5 3 2 = -198
#guard parabolaDirectrix 9 8 4 = -2336
#guard parabolaDirectrix 2 4 6 = -130
