import Batteries

open Std

def chineseZodiac (year : Nat) : String :=
  let r := (year + 12*2000 - 2000) % 12
  if r == 0 then "Dragon"
  else if r == 1 then "Snake"
  else if r == 2 then "Horse"
  else if r == 3 then "sheep"
  else if r == 4 then "Monkey"
  else if r == 5 then "Rooster"
  else if r == 6 then "Dog"
  else if r == 7 then "Pig"
  else if r == 8 then "Rat"
  else if r == 9 then "Ox"
  else if r == 10 then "Tiger"
  else "Hare"

#guard chineseZodiac 1997 = "Ox"
#guard chineseZodiac 1998 = "Tiger"
#guard chineseZodiac 1994 = "Dog"
