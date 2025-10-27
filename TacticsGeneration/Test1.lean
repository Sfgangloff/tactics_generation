import Batteries

/- For this first test, we just fed the following prompts to GPT-5.

Comments: In general, it seems the coding agent doesn't care about efficiency at all
-- easily implementing an exponential solution, when it could be solved in linear time.
Part of it is because it tries to do it in a clean functional programming style,
while it could be using all the imperative programming features (let mut, for loop,
Arrays, ...)
-/

open Std

-- Prompt 1: Write a function to find the minimum cost path to reach (m, n) from (0, 0) for the given cost matrix cost[][] and a position (m, n) in cost[][]. At each step, the path can go down, right, or diagonally down-right.

-- Code 1:
def get2D? (grid : List (List Nat)) (i j : Nat) : Option Nat := do
  let row ← grid.get? i
  row.get? j

def INF : Nat := 1000000000

def minCost (grid : List (List Nat)) : Nat → Nat → Nat
| i, j =>
  match get2D? grid i j with
  | none      => INF
  | some cost =>
      if i = 0 ∧ j = 0 then
        cost
      else
        let up   := if i = 0 then INF else minCost (i - 1) j
        let left := if j = 0 then INF else minCost i (j - 1)
        let diag := if i = 0 ∨ j = 0 then INF else minCost (i - 1) (j - 1)
        cost + Nat.min (Nat.min up left) diag

-- Seems almost working, it forgets to insert the grid argument again.

#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16

-- Prompt 2: Write a function to find the shared elements from the given two lists.

-- Code 2:
def sharedElements [BEq α] (xs ys : List α) : List α :=
  xs.filter (fun x => ys.contains x)

def sharedElementsUnique [BEq α] (xs ys : List α) : List α :=
  (xs.filter (fun x => ys.contains x)).eraseDups

-- In my version, it doesn't compile unless I set the following (but sometimes
-- it is the default)
-- set_option autoImplicit true

#guard sharedElementsUnique [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard sharedElementsUnique [1, 2, 3, 4] [5, 4, 3, 7] == HashSet.ofList [3, 4]
#guard sharedElementsUnique [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]

-- Prompt 3: Write a Lean function to identify non-prime numbers.

-- Code 3:
def isPrime (n : Nat) : Bool :=
  n ≥ 2 ∧ (List.range (n - 2)).all (fun i => n % (i + 2) ≠ 0)

def isNonPrime (n : Nat) : Bool :=
  ¬ isPrime n

-- Fair, it could go just to the square root as in the python version but reasonable solution.

#guard isNonPrime 2 == false
#guard isNonPrime 10 == true
#guard isNonPrime 35 == true
#guard isNonPrime 37 == false

-- Prompt 4: Write a function to find the largest integers from a given list of numbers using heap queue algorithm

-- Code 4:
def insertHeap (x : Int) (heap : List Int) (k : Nat) : List Int :=
  let newHeap := (x :: heap).qsort (· > ·)
  newHeap.take k

def kLargest (xs : List Int) (k : Nat) : List Int :=
  xs.foldl (fun heap x => insertHeap x heap k) []

-- List do not have qsort -- List has a mergeSort, and Array has a qsort. As usual, the efficiency is terrible, resorting an array each insertion is not at all the heap algorithm.

#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == [85, 75, 65]
#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == [85, 75]
#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [85, 75, 65, 58, 35]


-- Prompt 5: Write a function to find the number of ways to fill it with 2 x 1 dominoes for the given 3 x n board.

-- Code 5:
def tilings3xN (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0
  | n+4 =>
    -- for n+4 ≥ 4:
    -- if n+4 is odd → 0; if even → iterate the recurrence a(k)=4a(k-2)-a(k-4)
    if (n+4) % 2 = 1 then
      0
    else
      -- We want a(4 + 2*t) where t = (n+4 - 4)/2 = n/2
      let t := n / 2
      let rec iter : Nat → Nat → Nat → Nat
        | 0, a_nm4, a_nm2 => 4 * a_nm2 - a_nm4      -- gives a(4) from a(0), a(2)
        | t+1, a_nm4, a_nm2 =>
            let a_k := 4 * a_nm2 - a_nm4            -- a(k) with k advancing by 2
            iter t a_nm2 a_k
      iter t 1 3

-- Good time complexity. I would argue writing this in an imperative manner would be more readable anyway.

-- Prompt 6: Write a Lean function to check whether the two numbers differ at one bit position only or not.

-- Code 6:
def differByOneBit (a b : Nat) : Bool :=
  let x := a xor b           -- bits that differ
  x ≠ 0 ∧ (x &&& (x - 1)) = 0
  -- a power-of-two test: x is non-zero and has exactly one 1-bit

-- `xor` is not a binary operator, `^^^` is.

-- Prompt 7: Write a function to find all words which are at least 4 characters long in a string. Words are formed by consecutive characters separated by spaces.

-- Code 7:
def wordsAtLeast4 (s : String) : List String :=
  s.split (· = ' ')
   |>.filter (fun w => w.length ≥ 4)
   |>.filter (fun w => w ≠ "")   -- remove empty strings (from multiple spaces)

-- Prompt 8: Write a function to find squares of individual elements in a list using lambda function.
-- Code 8:
def squareList (xs : List Int) : List Int :=
  xs.map (fun x => x * x)

-- Great (this is really easy in a functional language).


-- Prompt 9: Write a Lean function to find the minimum number of rotations required to get the same string.

-- Code 9:
def rotateLeftChars (cs : List Char) (k : Nat) : List Char :=
  let n := cs.length
  if n = 0 then cs
  else
    let k' := k % n
    cs.drop k' ++ cs.take k'

def minRotationsToOriginal (s : String) : Nat :=
  let cs := s.data
  let n  := cs.length
  if n = 0 then 0
  else
    let rec loop (k : Nat) : Nat :=
      if k = n then n
      else if rotateLeftChars cs k = cs then k
      else loop (k + 1)
    loop 1

-- It needs to add `partial`.


-- Prompt 10: Write a function to get the n smallest items from a dataset.

-- Code 10:
def kSmallest [Ord α] (xs : List α) (k : Nat) : List α :=
  (xs.qsort (· < ·)).take k

def nSmallestInts (xs : List Int) (n : Nat) : List Int :=
  kSmallest xs n

-- Besides non-existent List.qsort (it should use mergeSort), it is getting lost on the typeclasses (and no need for it here, it would be enough to use Int, rather than a general type α).
