import Batteries
open Std

inductive PyVal
| int (n : Nat)
| tup (xs : List PyVal)
  deriving Repr, Inhabited

mutual
  def decEqPyVal (a b : PyVal) : Decidable (a = b) :=
    match a, b with
    | PyVal.int n, PyVal.int m =>
        if h : n = m then
          isTrue (by cases h; rfl)
        else
          isFalse (by
            intro h'
            cases h'
            exact h rfl)
    | PyVal.tup xs, PyVal.tup ys =>
        match decEqListPyVal xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by
            intro h'
            cases h'
            exact h rfl)
    | PyVal.int _, PyVal.tup _ => isFalse (by intro h; cases h)
    | PyVal.tup _, PyVal.int _ => isFalse (by intro h; cases h)
  def decEqListPyVal (xs ys : List PyVal) : Decidable (xs = ys) :=
    match xs, ys with
    | [], [] => isTrue rfl
    | [], _::_ => isFalse (by intro h; cases h)
    | _::_, [] => isFalse (by intro h; cases h)
    | x::xs', y::ys' =>
        match decEqPyVal x y with
        | isTrue hx =>
            match decEqListPyVal xs' ys' with
            | isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
            | isFalse hxs =>
                isFalse (by
                  intro h
                  cases h
                  exact hxs rfl)
        | isFalse hx =>
            isFalse (by
              intro h
              cases h
              exact hx rfl)
end

instance : DecidableEq PyVal := fun a b => decEqPyVal a b

mutual
  def evenEle (t : PyVal) (evenFnc : Nat → Bool) : PyVal :=
    match t with
    | PyVal.int _ => PyVal.tup []
    | PyVal.tup xs => PyVal.tup (processList xs evenFnc)

  def processList (ys : List PyVal) (evenFnc : Nat → Bool) : List PyVal :=
    match ys with
    | [] => []
    | y :: ys' =>
        let rest := processList ys' evenFnc
        match y with
        | PyVal.int n => if evenFnc n then PyVal.int n :: rest else rest
        | PyVal.tup zs => evenEle (PyVal.tup zs) evenFnc :: rest
end

def extractEven (testTuple : PyVal) : PyVal :=
  let res := evenEle testTuple (fun x => x % 2 == 0)
  res

#guard extractEven (PyVal.tup [PyVal.int 4, PyVal.int 5, PyVal.tup [PyVal.int 7, PyVal.int 6, PyVal.tup [PyVal.int 2, PyVal.int 4]], PyVal.int 6, PyVal.int 8]) =
  PyVal.tup [PyVal.int 4, PyVal.tup [PyVal.int 6, PyVal.tup [PyVal.int 2, PyVal.int 4]], PyVal.int 6, PyVal.int 8]

#guard extractEven (PyVal.tup [PyVal.int 5, PyVal.int 6, PyVal.tup [PyVal.int 8, PyVal.int 7, PyVal.tup [PyVal.int 4, PyVal.int 8]], PyVal.int 7, PyVal.int 9]) =
  PyVal.tup [PyVal.int 6, PyVal.tup [PyVal.int 8, PyVal.tup [PyVal.int 4, PyVal.int 8]]]

#guard extractEven (PyVal.tup [PyVal.int 5, PyVal.int 6, PyVal.tup [PyVal.int 9, PyVal.int 8, PyVal.tup [PyVal.int 4, PyVal.int 6]], PyVal.int 8, PyVal.int 10]) =
  PyVal.tup [PyVal.int 6, PyVal.tup [PyVal.int 8, PyVal.tup [PyVal.int 4, PyVal.int 6]], PyVal.int 8, PyVal.int 10]
