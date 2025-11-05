import Batteries
open Std

def hmGetOrDefault (m : HashMap String Nat) (k : String) (d : Nat) : Nat :=
  match m.toList.find? (fun p => p.fst == k) with
  | some p => p.snd
  | none => d

def maxAggregate (stdata : List (String × Nat)) : (String × Nat) := Id.run do
  
  let mut temp : HashMap String Nat := {}
  for (nm, marks) in stdata do
    let cur := hmGetOrDefault temp nm 0
    temp := temp.insert nm (cur + marks)
  let mut best : Option (String × Nat) := none
  for (nm, total) in temp.toList do
    match best with
    | none => best := some (nm, total)
    | some (_, bt) =>
        if total > bt then
          best := some (nm, total)
        else
          ()
  return match best with
  | some p => p
  | none => ("", 0)

#guard maxAggregate [("Juan Whelan",90),("Sabah Colley",88),("Peter Nichols",7),("Juan Whelan",122),("Sabah Colley",84)] = ("Juan Whelan", 212)
#guard maxAggregate [("Juan Whelan",50),("Sabah Colley",48),("Peter Nichols",37),("Juan Whelan",22),("Sabah Colley",14)] = ("Juan Whelan", 72)
#guard maxAggregate [("Juan Whelan",10),("Sabah Colley",20),("Peter Nichols",30),("Juan Whelan",40),("Sabah Colley",50)] = ("Sabah Colley", 70)
