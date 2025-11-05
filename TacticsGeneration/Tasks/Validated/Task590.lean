import Batteries
open Std

def polar_rect (x y : Nat) : ((Float × Float) × (Float × Float)) :=
  let fx := Float.ofInt (Int.ofNat x)
  let fy := Float.ofInt (Int.ofNat y)
  let r  := Float.sqrt (fx*fx + fy*fy)
  
  let phi := Float.atan2 fy fx
  let cn  := (r, phi)
  
  let re  : Float := -2.0
  let im  : Float := 0.0
  let cn1 := (re, im)
  (cn, cn1)

def fAbs (x : Float) : Float := if x >= 0.0 then x else -x

def almostEq (a b eps : Float) : Bool :=
  if fAbs (a - b) <= eps then true else false

def pairAlmostEq (p q : Float × Float) (eps : Float) : Bool :=
  almostEq p.fst q.fst eps && almostEq p.snd q.snd eps

def eps : Float := 1.0e-12

def r1 := polar_rect 3 4
#guard pairAlmostEq r1.fst (5.0, 0.9272952180016122) eps &&
       pairAlmostEq r1.snd (-2.0, 2.4492935982947064e-16) eps

def r2 := polar_rect 4 7
#guard pairAlmostEq r2.fst (8.06225774829855, 1.0516502125483738) eps &&
       pairAlmostEq r2.snd (-2.0, 2.4492935982947064e-16) eps

def r3 := polar_rect 15 17
#guard pairAlmostEq r3.fst (22.67156809750927, 0.8478169733934057) eps &&
       pairAlmostEq r3.snd (-2.0, 2.4492935982947064e-16) eps
