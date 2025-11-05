import Batteries
open Std

def tupString (tup1 : List Char) : String := String.mk tup1

#guard tupString ['e', 'x', 'e', 'r', 'c', 'i', 's', 'e', 's'] == "exercises"
#guard tupString ['p', 'y', 't', 'h', 'o', 'n'] == "python"
#guard tupString ['p', 'r', 'o', 'g', 'r', 'a', 'm'] == "program"
