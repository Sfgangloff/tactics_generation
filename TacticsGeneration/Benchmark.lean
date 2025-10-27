import Batteries

open Std

-- Prompt 1: Write a function to find the minimum cost path to reach (m, n) from (0, 0) for the given cost matrix cost[][] and a position (m, n) in cost[][]. At each step, the path can go down, right, or diagonally down-right.
-- (updated) The last sentence was added since the original problem statement was incomplete.

-- Code 1:
def Array.modify2d {α : Type} (a : Array (Array α)) (y x : Nat) (f : α → α) :=
  a.modify y <| fun row => row.modify x f

def Array.set2d? {α : Type} (a : Array (Array α)) (y x : Nat) (value : α) :=
  a.modify2d y x (fun _ => value)

def List.get2d {α : Type} (l : List (List α)) (y x : Nat) (fallback : α) :=
  (l.getD y []).getD x fallback

def Array.get2d {α : Type} (a : Array (Array α)) (y x : Nat) (fallback : α) :=
  (a.getD y #[]).getD x fallback

def minCost (cost : List (List Nat)) (m n : Nat) : Nat := Id.run do
  let mut tc : Array (Array Nat) :=
    Array.replicate (m+1) (Array.replicate (n+1) 0)
  tc := tc.set2d? 0 0 (cost.get2d 0 0 0)
  for i in [1 : m+1] do
    tc := tc.set2d? i 0 <| tc.get2d (i-1) 0 0 + cost.get2d i 0 0
  for j in [1 : n+1] do
    tc := tc.set2d? 0 j <| tc.get2d 0 (j-1) 0 + cost.get2d 0 j 0
  for i in [1 : m+1] do
    for j in [1 : n+1] do
      tc := tc.set2d? i j <|
        min (tc.get2d (i-1) (j-1) 0) (
          min (tc.get2d (i-1) j 0) (tc.get2d i (j-1) 0)
        ) + cost.get2d i j 0
  return tc.get2d m n 0

-- Tests 1:
#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16

-- Prompt 2: Write a function to find the shared elements from the given two lists.

-- Code 2:
def similarElements (l1 l2 : List Int) : HashSet Int := Id.run do
  let s1 := HashSet.ofList l1
  let s2 := HashSet.ofList l2
  return s1.filter (fun x => x ∈ s2)

-- Tests 2:
#guard similarElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard similarElements [1, 2, 3, 4] [5, 4, 3, 7] == HashSet.ofList [3, 4]
#guard similarElements [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]

-- Prompt 3: Write a Lean function to identify non-prime numbers.

-- Code 3:
def isNotPrime (n : Nat) : Bool := Id.run do
  for x in [2 : Nat.sqrt n + 1] do
    if n % x == 0 then return true
  return false

-- Tests 3:
#guard isNotPrime 2 == false
#guard isNotPrime 10 == true
#guard isNotPrime 35 == true
#guard isNotPrime 37 == false

-- Prompt 4: Write a function to find the largest integers from a given list of numbers using heap queue algorithm

-- Code 4:
def heapQueueLargest (nums : List Nat) (n : Nat) : List Nat := Id.run do
  let mut heap := nums.toArray.toBinaryHeap (· < ·)
  let mut res := #[]
  for _ in [: n] do
    match heap.max with
    | none => break
    | some x => res := res.push x
    heap := heap.popMax
  return res.toList

-- Tests 4:
#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == [85, 75, 65]
#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == [85, 75]
#guard heapQueueLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [85, 75, 65, 58, 35]

-- Prompt 5: Write a function to find the number of ways to fill it with 2 x 1 dominoes for the given 3 x n board.

-- Code 5:
def countWays (n : Nat) : Nat := Id.run do
  let mut A := Array.replicate (n+1) 0
  let mut B := Array.replicate (n+1) 0
  A := A.modify 0 (fun _ => 1)
  A := A.modify 1 (fun _ => 0)
  B := B.modify 0 (fun _ => 0)
  B := B.modify 1 (fun _ => 1)
  for i in [2 : n+1] do
    A := A.set! i <| A[i-2]! + 2*B[i-1]!
    B := B.set! i <| A[i-1]! + B[i-2]!
  return A[n]!

-- Tests 5:
#guard countWays 2 == 3
#guard countWays 8 == 153
#guard countWays 12 == 2131

-- Prompt 6: Write a Lean function to check whether the two numbers differ at one bit position only or not.

-- Code 6:
def isPowerOfTwo (x : Nat) : Bool := x != 0 && (x &&& x-1) == 0
def differAtOneBitPos (a b : Nat) := isPowerOfTwo (a ^^^ b)

-- Tests 6:
#guard differAtOneBitPos 13 9 == true
#guard differAtOneBitPos 15 8 == false
#guard differAtOneBitPos 2 4 == false

-- Prompt 7: Write a function to find all words which are at least 4 characters long in a string. Words are formed by consecutive characters separated by spaces.
-- (updated) Lean doesn't have Regex string matching, so we simplified the statements.

-- Code 7:
def findLongWords (text : String) : List String :=
  text.splitOn.filter (fun x => x.length >= 4)

-- Tests 7:
#guard findLongWords "Please move back to stream" == ["Please", "move", "back", "stream"]
#guard findLongWords "Jing Eco and Tech" == ["Jing", "Tech"]
#guard findLongWords "Jhingai wulu road Zone 3" == ["Jhingai", "wulu", "road", "Zone"]

-- Prompt 8: Write a function to find squares of individual elements in a list using lambda function.

-- Code 8:
def squareNums (nums : List Nat) : List Nat := nums.map (fun x => x ^ 2)

-- Tests 8:
#guard squareNums [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] == [1, 4, 9, 16, 25, 36, 49, 64, 81, 100]
#guard squareNums [10,20,30] == [100,400,900]
#guard squareNums [12,15] == [144,225]

-- Prompt 9: Write a Lean function to find the minimum number of rotations required to get the same string.

-- Code 9:
def findRotations (str : String) : Nat := Id.run do
  let tmp := str ++ str
  let n := str.utf8ByteSize
  for i in [1 : n + 1] do
    let pos : String.Pos := ⟨i⟩
    if !pos.isValid str then continue
    let substring : Substring := {str := tmp, startPos := pos, stopPos := ⟨i+n⟩}
    if str == substring then return i
  return n

-- Tests 9:
#guard findRotations "aaaa" == 1
#guard findRotations "ab" == 2
#guard findRotations "abc" == 3

-- Prompt 10: Write a function to get the n smallest items from a dataset.

-- Code 10:
def smallNNum (list1 : List Nat) (n : Nat) : List Nat := Id.run do
  let mut heap := list1.toArray.toBinaryHeap (· > ·)
  let mut res := #[]
  for _ in [: n] do
    match heap.max with
    | none => break
    | some x => res := res.push x
    heap := heap.popMax
  return res.toList

-- Tests 10:
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [10,20]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [10,20,20,40,50]
#guard smallNNum [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [10,20,20]
