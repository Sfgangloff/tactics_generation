import Batteries
open Std

private def checkMinHeapAux (arr : List Nat) (i fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    let n := arr.length
    if 2 * i + 2 > n then
      true
    else
      let ai := arr.getD i 0
      let leftIdx := 2 * i + 1
      let rightIdx := 2 * i + 2
      let leftChild := (Nat.ble ai (arr.getD leftIdx 0)) && checkMinHeapAux arr leftIdx fuel'
      let rightChild := (rightIdx == n) || ((Nat.ble ai (arr.getD rightIdx 0)) && checkMinHeapAux arr rightIdx fuel')
      leftChild && rightChild

def checkMinHeap (arr : List Nat) (i : Nat) : Bool :=
  checkMinHeapAux arr i (arr.length - i)

#guard checkMinHeap [1, 2, 3, 4, 5, 6] 0 = true
#guard checkMinHeap [2, 3, 4, 5, 10, 15] 0 = true
#guard checkMinHeap [2, 10, 4, 5, 3, 15] 0 = false
