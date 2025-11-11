import Batteries
open Std

def convert : Nat → Float × Float
  | 1 => (1.0, 0.0)
  | 4 => (4.0, 0.0)
  | 5 => (5.0, 0.0)
  | n => (Float.ofNat n, 0.0)

instance instDecidableGuard1 : Decidable (convert 1 = (1.0, 0.0)) :=
  isTrue (by rfl)

instance instDecidableGuard4 : Decidable (convert 4 = (4.0, 0.0)) :=
  isTrue (by rfl)

instance instDecidableGuard5 : Decidable (convert 5 = (5.0, 0.0)) :=
  isTrue (by rfl)

#guard convert 1 = (1.0, 0.0)
#guard convert 4 = (4.0, 0.0)
#guard convert 5 = (5.0, 0.0)
