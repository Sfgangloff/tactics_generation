import Batteries

open Std

def isPowerOfTwo (x : Nat) : Bool := x != 0 && (x &&& (x - 1)) == 0
def differAtOneBitPos (a b : Nat) := isPowerOfTwo (a ^^^ b)

#guard differAtOneBitPos 13 9 == true
#guard differAtOneBitPos 15 8 == false
#guard differAtOneBitPos 2 4 == false
