import Batteries

open Std

inductive Enc (α : Type u) where
  | one : α → Enc α
  | many : Nat → α → Enc α
  deriving Repr, DecidableEq

private def packEnc (cnt : Nat) (x : α) : Enc α :=
  if cnt > 1 then Enc.many cnt x else Enc.one x

def modifiedEncode {α : Type u} [DecidableEq α] (alist : List α) : List (Enc α) :=
  match alist with
  | [] => []
  | x :: xs =>
    let rec loop (cur : α) (cnt : Nat) (rest : List α) (acc : List (Enc α)) : List (Enc α) :=
      match rest with
      | [] => (packEnc cnt cur :: acc).reverse
      | y :: ys =>
        if y = cur then
          loop cur (cnt + 1) ys acc
        else
          loop y 1 ys (packEnc cnt cur :: acc)
    loop x 1 xs []

#guard modifiedEncode [1,1,2,3,4,4,5,1] = [Enc.many 2 1, Enc.one 2, Enc.one 3, Enc.many 2 4, Enc.one 5, Enc.one 1]

#guard modifiedEncode ("automatically".data) = [
  Enc.one 'a', Enc.one 'u', Enc.one 't', Enc.one 'o', Enc.one 'm', Enc.one 'a',
  Enc.one 't', Enc.one 'i', Enc.one 'c', Enc.one 'a', Enc.many 2 'l', Enc.one 'y'
]

#guard modifiedEncode ("python".data) = [
  Enc.one 'p', Enc.one 'y', Enc.one 't', Enc.one 'h', Enc.one 'o', Enc.one 'n'
]
