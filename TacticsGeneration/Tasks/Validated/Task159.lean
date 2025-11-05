import Batteries

open Std

def monthSeason (month : String) (days : Nat) : String :=
  let season0 :=
    if month == "January" || month == "February" || month == "March" then
      "winter"
    else if month == "April" || month == "May" || month == "June" then
      "spring"
    else if month == "July" || month == "August" || month == "September" then
      "summer"
    else
      "autumn"
  let season1 :=
    if (month == "March") && Nat.blt 19 days then
      "spring"
    else if (month == "June") && Nat.blt 20 days then
      "summer"
    else if (month == "September") && Nat.blt 21 days then
      "autumn"
    else if (month == "October") && Nat.blt 21 days then
      "autumn"
    else if (month == "November") && Nat.blt 21 days then
      "autumn"
    else if (month == "December") && Nat.blt 20 days then
      "winter"
    else
      season0
  season1

#guard monthSeason "January" 4 == "winter"
#guard monthSeason "October" 28 == "autumn"
#guard monthSeason "June" 6 == "spring"
