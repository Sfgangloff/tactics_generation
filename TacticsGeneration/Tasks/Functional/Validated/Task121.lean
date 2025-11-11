import Batteries
open Std

def checkTriplet (A : List Int) : Nat → Int → Nat → Bool
| 0, sum, count => count == 3 && sum == 0
| n+1, sum, count =>
  if count == 3 then
    sum == 0
  else if sum < 0 then
    false
  else
    let a_n := A.getD n 0
    checkTriplet A n (sum - a_n) (count + 1) ||
    checkTriplet A n sum count

#guard checkTriplet [2, 7, 4, 0, 9, 5, 1, 3] 8 6 0 == true
#guard checkTriplet [1, 4, 5, 6, 7, 8, 5, 9] 8 6 0 == false
#guard checkTriplet [10, 4, 2, 3, 5] 5 15 0 == true
