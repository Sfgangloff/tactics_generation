import Batteries
open Std

structure Node where
  data : Nat
  left : Option Node := none
  right : Option Node := none

private def maxHeightFuel (fuel : Nat) (node : Option Node) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    match node with
    | none => 0
    | some n =>
      let leftHeight := maxHeightFuel fuel' n.left
      let rightHeight := maxHeightFuel fuel' n.right
      if leftHeight > rightHeight then leftHeight + 1 else rightHeight + 1

def max_height (node : Node) : Nat :=
  maxHeightFuel 1000000 (some node)

def root : Task927.Node :=
  { data := 1
  , left := some { data := 2, left := some { data := 4 }, right := some { data := 5 } }
  , right := some { data := 3 }
  }

def root1 : Task927.Node :=
  { data := 1
  , left := some { data := 2, left := some { data := 4 } }
  , right := some {
      data := 3,
      left := some { data := 5 },
      right := some {
        data := 6,
        right := some {
          data := 7,
          right := some { data := 8 }
        }
      }
    }
  }

def root2 : Task927.Node :=
  { data := 1
  , left := some {
      data := 2,
      left := some { data := 4, left := some { data := 6 }, right := some { data := 7 } },
      right := some { data := 5 }
    },
    right := some { data := 3 }
  }

#guard max_height root = 3
#guard max_height root1 = 5
#guard max_height root2 = 4
