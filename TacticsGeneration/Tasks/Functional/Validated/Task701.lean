import Batteries

open Std

def equilibriumIndex (arr : List Int) : Int := Id.run do
  let mut totalSum := arr.foldl (fun acc x => acc + x) (0 : Int)
  let mut leftSum : Int := 0
  let mut i : Int := 0
  for num in arr do
    totalSum := totalSum - num
    if leftSum == totalSum then
      return i
    leftSum := leftSum + num
    i := i + 1
  return (-1)

#guard equilibriumIndex [1, 2, 3, 4, 1, 2, 3] = 3
#guard equilibriumIndex [-7, 1, 5, 2, -4, 3, 0] = 3
#guard equilibriumIndex [1, 2, 3] = -1
