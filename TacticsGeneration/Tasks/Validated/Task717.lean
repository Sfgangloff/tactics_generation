import Batteries

open Std

def avg_calc (ls : List Float) : Float :=
  
  
  let n := ls.length
  if n <= 1 then
    ls.headD 0.0
  else
    let sum := ls.foldl (fun acc el => acc + el) 0.0
    sum / Float.ofNat n

def sd_calc (data : List Float) : Float :=
  let n := data.length
  if n <= 1 then
    0.0
  else
    let mean := avg_calc data
    let ssum := data.foldl (fun acc el => acc + (el - mean) * (el - mean)) 0.0
    Float.sqrt (ssum / Float.ofNat (n - 1))

#guard sd_calc [4.0, 2.0, 5.0, 8.0, 6.0] == 2.23606797749979
#guard sd_calc [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0] == 2.160246899469287
#guard sd_calc [5.0, 9.0, 10.0, 15.0, 6.0, 4.0] == 4.070217029430577
