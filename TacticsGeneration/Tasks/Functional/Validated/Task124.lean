import Batteries

open Std

def angleComplex (a b : Float) : Float := Float.atan2 b a

#guard angleComplex 0 1 == 1.5707963267948966
#guard angleComplex 2 1 == 0.4636476090008061
#guard angleComplex 0 2 == 1.5707963267948966
