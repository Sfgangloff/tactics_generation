import Batteries

open Std

def harmonicSum : Nat -> Float
| 0 => 1.0
| 1 => 1.0
| n+2 => (1.0 / Float.ofNat (n+2)) + harmonicSum (n+1)

#guard harmonicSum 10 == (2.9289682539682538 : Float)
#guard harmonicSum 4 == (2.083333333333333 : Float)
#guard harmonicSum 7 == (2.5928571428571425 : Float)
