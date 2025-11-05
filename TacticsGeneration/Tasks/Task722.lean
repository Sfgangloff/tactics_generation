import Batteries
open Std

def filterData (students : List (String × (Float × Nat))) (h : Float) (w : Nat) : List (String × (Float × Nat)) :=
  students.filter (fun (_k, s) =>
    let c1 : Bool :=
      match Float.cmp s.fst h with
      | Ordering.lt => false
      | _ => true
    let c2 : Bool := Nat.ble w s.snd
    c1 && c2)

#guard filterData [("Cierra Vega", ((6.2 : Float), 70)), ("Alden Cantrell", ((5.9 : Float), 65)), ("Kierra Gentry", ((6.0 : Float), 68)), ("Pierre Cox", ((5.8 : Float), 66))] (6.0 : Float) 70 = [("Cierra Vega", ((6.2 : Float), 70))]
#guard filterData [("Cierra Vega", ((6.2 : Float), 70)), ("Alden Cantrell", ((5.9 : Float), 65)), ("Kierra Gentry", ((6.0 : Float), 68)), ("Pierre Cox", ((5.8 : Float), 66))] (5.9 : Float) 67 = [("Cierra Vega", ((6.2 : Float), 70)), ("Kierra Gentry", ((6.0 : Float), 68))]
#guard filterData [("Cierra Vega", ((6.2 : Float), 70)), ("Alden Cantrell", ((5.9 : Float), 65)), ("Kierra Gentry", ((6.0 : Float), 68)), ("Pierre Cox", ((5.8 : Float), 66))] (5.7 : Float) 64 = [("Cierra Vega", ((6.2 : Float), 70)), ("Alden Cantrell", ((5.9 : Float), 65)), ("Kierra Gentry", ((6.0 : Float), 68)), ("Pierre Cox", ((5.8 : Float), 66))]
