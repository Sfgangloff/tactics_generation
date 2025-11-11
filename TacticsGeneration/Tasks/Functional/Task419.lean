import Batteries
open Std

def roundAndSum (list1 : List Float) : Int :=
  let lenght := list1.length
  let rounded : List Int :=
    list1.map (fun x =>
      if x >= (0.0 : Float) then
        Real.floor ((x : Real) + (0.5 : Real))
      else
        Real.ceil ((x : Real) - (0.5 : Real)))
  let repeated : List Int := List.join (List.replicate lenght rounded)
  repeated.foldl (fun s x => s + x) (0 : Int)

#guard roundAndSum [22.4, 4.0, -16.22, -9.10, 11.00, -12.22, 14.20, -5.20, 17.50] = 243
#guard roundAndSum [5.0, 2.0, 9.0, 24.3, 29.0] = 345
#guard roundAndSum [25.0, 56.7, 89.2] = 513
