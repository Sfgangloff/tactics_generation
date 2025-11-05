import Batteries

open Std

def reverseStringList (stringlist : List String) : List String :=
  stringlist.map (fun x => String.mk (x.data.reverse))

#guard reverseStringList ["Red", "Green", "Blue", "White", "Black"] = ["deR", "neerG", "eulB", "etihW", "kcalB"]
#guard reverseStringList ["john","amal","joel","george"] = ["nhoj","lama","leoj","egroeg"]
#guard reverseStringList ["jack","john","mary"] = ["kcaj","nhoj","yram"]
