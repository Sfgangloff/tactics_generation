import Batteries

open Std

def setMiddleBits (n : Nat) : Nat := Id.run do
  let mut m := n
  m := m ||| (m >>> 1)
  m := m ||| (m >>> 2)
  m := m ||| (m >>> 4)
  m := m ||| (m >>> 8)
  m := m ||| (m >>> 16)
  return (m >>> 1) ^^^ 1

def toggleMiddleBits (n : Nat) : Nat :=
  if n == 1 then 1 else n ^^^ setMiddleBits n

#guard toggleMiddleBits 9 = 15
#guard toggleMiddleBits 10 = 12
#guard toggleMiddleBits 11 = 13
