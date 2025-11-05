import Batteries

open Std

def insertInt (x : Int) : List Int → List Int
| [] => [x]
| y :: ys =>
  match compare x y with
  | Ordering.lt => x :: y :: ys
  | Ordering.eq => x :: y :: ys
  | Ordering.gt => y :: insertInt x ys

def isortInt : List Int → List Int
| [] => []
| x :: xs => insertInt x (isortInt xs)

def sortNumericStrings (nums_str : List String) : List Int :=
  let result := nums_str.map (fun s => (s.trim.toInt?).getD 0)
  isortInt result

#guard sortNumericStrings ["4","12","45","7","0","100","200","-12","-500"] = [-500, -12, 0, 4, 7, 12, 45, 100, 200]
#guard sortNumericStrings ["2","3","8","4","7","9","8","2","6","5","1","6","1","2","3","4","6","9","1","2"] = [1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 5, 6, 6, 6, 7, 8, 8, 9, 9]
#guard sortNumericStrings ["1","3","5","7","1", "3","13", "15", "17","5", "7 ","9","1", "11"] = [1, 1, 1, 3, 3, 5, 5, 7, 7, 9, 11, 13, 15, 17]
