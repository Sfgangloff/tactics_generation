import Batteries


/- We try here to recursively feedback the errors to the model in order to arrive at an actual solution.
-/

open Std

-- Prompt 1: Write a function to find the minimum cost path to reach (m, n) from (0, 0) for the given cost matrix cost[][] and a position (m, n) in cost[][]. At each step, the path can go down, right, or diagonally down-right.

-- Code 1:
def INF : Nat := 1_000_000_000

def listGet? {α} : List α → Nat → Option α
| [],      _     => none
| x :: _,  0     => some x
| _ :: xs, n+1   => listGet? xs n

def get2D?_list (grid : List (List Nat)) (i j : Nat) : Option Nat := do
  let row ← listGet? grid i
  listGet? row j

partial def minCost (grid : List (List Nat)) : Nat → Nat → Nat
| i, j =>
  match get2D?_list grid i j with
  | none      => INF
  | some cost =>
    if i = 0 ∧ j = 0 then
      cost
    else
      let up   := if i = 0 then INF else minCost grid (i - 1) j
      let left := if j = 0 then INF else minCost grid i (j - 1)
      let diag := if i = 0 ∨ j = 0 then INF else minCost grid (i - 1) (j - 1)
      cost + Nat.min (Nat.min up left) diag

-- Corrected in two feedback steps (actually repeats the first error on ".get?").

#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16

-- Prompt 2: Write a function to find the shared elements from the given two lists.

-- Code 2:
def similarElements {α : Type} [BEq α] [Hashable α]
    (xs ys : List α) : HashSet α :=
  let setY : HashSet α := HashSet.ofList ys
  xs.foldl (init := ({} : HashSet α)) fun acc x =>
    if setY.contains x then acc.insert x else acc

#guard similarElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard similarElements [1, 2, 3, 4] [5, 4, 3, 7]  == HashSet.ofList [3, 4]
#guard similarElements [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]

-- 3-4 feedback iterations to get the oredered lists in the right format.

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
  let newHeap := (x :: heap).mergeSort (fun a b => decide (a > b)) -- descending
  List.take k newHeap   -- or: newHeap.take k

def kLargest (xs : List Int) (k : Nat) : List Int :=
  xs.foldl (fun heap x => insertHeap x heap k) []

-- Fixed in two feedback steps.

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

#guard tilings3xN 2 == 3
#guard tilings3xN 8 == 153
#guard tilings3xN 12 == 2131

-- Prompt 6: Write a Lean function to check whether the two numbers differ at one bit position only or not.

-- Code 6:
def differByOneBit (a b : Nat) : Bool :=
  let x := a ^^^ b           -- bits that differ
  x ≠ 0 ∧ (x &&& (x - 1)) = 0
  -- a power-of-two test: x is non-zero and has exactly one 1-bit

#guard differByOneBit 13 9 == true
#guard differByOneBit 15 8 == false
#guard differByOneBit 2 4 == false

-- Fixed in one feedback step, suggesting operator `^^^`.

-- Prompt 7: Write a function to find all words which are at least 4 characters long in a string. Words are formed by consecutive characters separated by spaces.

-- Code 7:
def wordsAtLeast4 (s : String) : List String :=
  s.split (· = ' ')
   |>.filter (fun w => w.length ≥ 4)
   |>.filter (fun w => w ≠ "")   -- remove empty strings (from multiple spaces)

#guard wordsAtLeast4 "Please move back to stream" == ["Please", "move", "back", "stream"]
#guard wordsAtLeast4 "Jing Eco and Tech" == ["Jing", "Tech"]
#guard wordsAtLeast4 "Jhingai wulu road Zone 3" == ["Jhingai", "wulu", "road", "Zone"]

-- Prompt 8: Write a function to find squares of individual elements in a list using lambda function.
-- Code 8:
def squareList (xs : List Int) : List Int :=
  xs.map (fun x => x * x)

#guard squareList [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
#guard squareList [10,20,30] == [100,400,900]
#guard squareList [12,15] == [144,225]

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
    -- loop t k: try at most t remaining steps, starting at rotation k
    let rec loop (t k : Nat) : Nat :=
      match t with
      | 0      => n
      | t + 1  =>
        if rotateLeftChars cs k = cs then
          k
        else
          loop t (k + 1)
    loop n 1

-- Fixed in one feedback step.

#guard minRotationsToOriginal "aaaa" == 1
#guard minRotationsToOriginal "ab" == 2
#guard minRotationsToOriginal "abc" == 3


-- Prompt 10: Write a function to get the n smallest items from a dataset.

-- Code 10:
def kSmallest [Ord α] (xs : List α) (k : Nat) : List α :=
  (xs.mergeSort (fun a b => compare a b == Ordering.lt)).take k

def nSmallestInts (xs : List Int) (n : Nat) : List Int :=
  kSmallest xs n

-- Fixed in three feedback steps (first step suggesting mergeSort, second and third, fixing some formatting
-- issue)

#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [10,20]
#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [10,20,20,40,50]
#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [10,20,20]
