import Batteries
open Std

def joinTuples (testList : List (List Nat)) : List (List Nat) := Id.run do
  let mut res : Array (Array Nat) := #[]
  for sub in testList do
    let subArr := sub.toArray
    match res.back? with
    | some last =>
      let last0 :=
        match last.toList with
        | h :: _ => h
        | [] => 0
      let sub0 :=
        match sub with
        | h :: _ => h
        | [] => 0
      if last0 == sub0 then
        let tail := subArr.extract 1 subArr.size
        let idx := res.size - 1
        res := res.set! idx (last ++ tail)
      else
        res := res.push subArr
    | none =>
      res := res.push subArr
  return res.toList.map (fun a => a.toList)

#guard joinTuples [[5, 6], [5, 7], [6, 8], [6, 10], [7, 13]] = [[5, 6, 7], [6, 8, 10], [7, 13]]
#guard joinTuples [[6, 7], [6, 8], [7, 9], [7, 11], [8, 14]] = [[6, 7, 8], [7, 9, 11], [8, 14]]
#guard joinTuples [[7, 8], [7, 9], [8, 10], [8, 12], [9, 15]] = [[7, 8, 9], [8, 10, 12], [9, 15]]
