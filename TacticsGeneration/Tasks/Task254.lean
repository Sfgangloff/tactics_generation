import Batteries
open Std

def isWordChar (c : Char) : Bool :=
  let n := c.toNat
  let isAZ := decide ('A'.toNat ≤ n) && decide (n ≤ 'Z'.toNat)
  let isaz := decide ('a'.toNat ≤ n) && decide (n ≤ 'z'.toNat)
  let is09 := decide ('0'.toNat ≤ n) && decide (n ≤ '9'.toNat)
  isaz || isAZ || is09 || (c == '_')

def takeWhileWordAux (cs : List Char) (accRev : List Char) : (List Char × List Char) :=
  match cs with
  | [] => (accRev.reverse, [])
  | c :: cs' =>
    if isWordChar c then
      takeWhileWordAux cs' (c :: accRev)
    else
      (accRev.reverse, c :: cs')

theorem takeWhileWordAux_rest_len_le (cs : List Char) (accRev : List Char) :
    ((takeWhileWordAux cs accRev).2.length ≤ cs.length) := by
  induction cs generalizing accRev with
  | nil =>
    simp [takeWhileWordAux]
  | cons c cs ih =>
    by_cases h : isWordChar c
    ·
      have h' := ih (accRev := c :: accRev)
      simpa [takeWhileWordAux, h, List.length] using
        Nat.le_trans h' (Nat.le_succ _)
    ·
      simp [takeWhileWordAux, h]

def loop (cs : List Char) (resRev : List String) : List String :=
  match cs with
  | [] => resRev.reverse
  | c :: cs' =>
    if c == 'a' || c == 'e' then
      let p := takeWhileWordAux cs' []
      let pref := p.fst
      let rest := p.snd
      match pref with
      | [] => loop cs' resRev
      | _ =>
        let s := String.mk (c :: pref)
        loop rest (s :: resRev)
    else
      loop cs' resRev
termination_by loop cs resRev => cs.length
decreasing_by
  simp_wf
  have hle := takeWhileWordAux_rest_len_le cs' []
  simpa [List.length] using Nat.lt_succ_of_le hle

def wordsAe (text : String) : List String :=
  loop text.data []

#guard wordsAe "python programe" == ["ame"]
#guard wordsAe "python programe language" == ["ame", "anguage"]
#guard wordsAe "assert statement" == ["assert", "atement"]
