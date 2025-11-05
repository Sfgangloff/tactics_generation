import Batteries

open Std

def centeredHexagonalNumber (n : Nat) : Nat := 3 * n * (n - 1) + 1

#guard centeredHexagonalNumber 10 == 271
#guard centeredHexagonalNumber 2 == 7
#guard centeredHexagonalNumber 9 == 217
