import Batteries

open Std

def palindromeLambda (texts : List String) : List String :=
  texts.filter (fun x => x == String.mk (x.toList.reverse))

#guard palindromeLambda ["php", "res", "Python", "abcd", "Java", "aaa"] = ["php", "aaa"]
#guard palindromeLambda ["abcd", "Python", "abba", "aba"] = ["abba", "aba"]
#guard palindromeLambda ["abcd", "abbccbba", "abba", "aba"] = ["abbccbba", "abba", "aba"]
