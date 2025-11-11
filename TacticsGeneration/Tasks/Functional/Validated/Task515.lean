import Batteries
open Std

def modular_sum (arr : List Nat) (n m : Nat) : Bool :=
  if n > m then
    true
  else
    if m = 0 then
      false
    else
      let arrN := arr.take n
      let rec go (xs : List Nat) (dp : Std.HashSet Nat) : Bool :=
        match xs with
        | [] => dp.contains 0
        | a :: xs' =>
          if dp.contains 0 then
            true
          else
            let temp : Std.HashSet Nat :=
              dp.fold (init := ({} : Std.HashSet Nat)) (fun acc j => acc.insert ((j + a) % m))
            let dp2 :=
              temp.fold (init := dp) (fun acc j => acc.insert j)
            let dp3 := dp2.insert (a % m)
            go xs' dp3
      go arrN ({} : Std.HashSet Nat)

#guard modular_sum [3, 1, 7, 5] 4 6 == true
#guard modular_sum [1, 7] 2 5 == false
#guard modular_sum [1, 6] 2 5 == false
