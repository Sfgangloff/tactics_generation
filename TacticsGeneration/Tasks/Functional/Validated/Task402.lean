import Batteries
open Std

def getAtNat : List Nat → Nat → Nat
| [], _ => 0
| x :: _, 0 => x
| _ :: xs, i+1 => getAtNat xs i

def setAtNat : List Nat → Nat → Nat → List Nat
| [], _, _ => []
| _ :: xs, 0, v => v :: xs
| x :: xs, i+1, v => x :: setAtNat xs i v

def ncrModp (n r p : Nat) : Nat :=
  let rec loopi : Nat → List Nat → List Nat
  | 0, C => C
  | i+1, C =>
    let upper := min (n - i) r
    let rec loopj : Nat → List Nat → List Nat
    | 0, Cj => Cj
    | j+1, Cj =>
      let vj := getAtNat Cj (j+1)
      let vjm1 := getAtNat Cj j
      let Cnext := setAtNat Cj (j+1) ((vj + vjm1) % p)
      loopj j Cnext
    let C1 := loopj upper C
    loopi i C1
  let C0 := List.replicate (r + 1) 0
  let C1 := setAtNat C0 0 1
  let Cfinal := loopi n C1
  getAtNat Cfinal r

#guard ncrModp 10 2 13 = 6
#guard ncrModp 15 12 43 = 25
#guard ncrModp 17 9 18 = 10
