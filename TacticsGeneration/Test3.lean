import Batteries


/- First attempt to maximize efficiency, by prompting the solutions of Test2, requesting to ameliorate
efficiency. After that we feedback errors to the LLM until arriving at an actual solution.
-/

open Std

-- Prompt 1: Write a function to find the minimum cost path to reach (m, n) from (0, 0) for the given cost matrix cost[][] and a position (m, n) in cost[][]. At each step, the path can go down, right, or diagonally down-right.

-- Code 1:
def INF : Nat := 1_000_000_000

/-- Safe list index. -/
def listGet? {α} : List α → Nat → Option α
| [],      _     => none
| x :: _,  0     => some x
| _ :: xs, n+1   => listGet? xs n

def min3 (a b c : Nat) : Nat := Nat.min (Nat.min a b) c

/-- Check all rows have length `w` (pure core recursion; no List.All). -/
def allLenEq {α} (w : Nat) : List (List α) → Bool
| []      => true
| r :: rs => (r.length = w) && allLenEq w rs

/-- If rectangular, return common width; otherwise `none`. -/
def widthOfRect? {α} : List (List α) → Option Nat
| []        => some 0
| r :: rs   =>
  let w := r.length
  if allLenEq w rs then some w else none

/-- DP for the first row (top edge): dp[0]=x₀; dp[j]=xⱼ + dp[j-1]. -/
def dpFirstRow : List Nat → List Nat
| []        => []
| x :: xs   =>
  let rec go (prev : Nat) : List Nat → List Nat
  | []        => [prev]
  | y :: ys   =>
      let cur := y + prev
      prev :: go cur ys
  go x xs

/-- Build row i from row (i-1) (called `upRow`) and the cost row i. -/
def dpNextRow : List Nat → List Nat → List Nat
| [],        _          => []                      -- degenerate; filtered upstream
| _ :: _,   []         => []                      -- degenerate; filtered upstream
| x :: xs,   u :: us    =>
  -- j = 0: only "up" is available on the first column
  let cur0 := x + u
  -- go left prevUp ys uss: produce cells j ≥ 1
  let rec go (left : Nat) (prevUp : Nat)
    : List Nat → List Nat → List Nat
  | [],        []          => [left]
  | y :: ys',  up' :: us'  =>
      let cur := y + min3 up' left prevUp
      left :: go cur up' ys' us'
  | [],        _           => [left]               -- for coverage; unreachable if rectangular
  | _ ,       []           => [left]               -- for coverage; unreachable if rectangular
  go cur0 u xs us

/-- Full DP table with same shape as `grid`. Returns `none` if grid is ragged. -/
def dpTable (grid : List (List Nat)) : Option (List (List Nat)) := do
  let w ← widthOfRect? grid
  match grid with
  | []        => some []
  | r0 :: rs  =>
    if w = 0 then
      some (List.replicate (rs.length + 1) [])
    else
      let dp0 := dpFirstRow r0
      let rec build (prev : List Nat) (rows : List (List Nat)) (acc : List (List Nat))
        : List (List Nat) :=
        match rows with
        | []       => (acc.reverse) ++ [prev]
        | r :: rs' =>
          let cur := dpNextRow r prev
          build cur rs' (prev :: acc)
      some (build dp0 rs [])

/-- Optimized version with the SAME signature as yours.
    Out-of-bounds or ragged grid returns `INF`. Runs in O(m·n) per call. -/
def minCost (grid : List (List Nat)) : Nat → Nat → Nat
| i, j =>
  match dpTable grid with
  | none      => INF
  | some dp   =>
    match listGet? dp i with
    | none      => INF
    | some row  =>
      match listGet? row j with
      | none     => INF
      | some v   => v

-- Corrected in five feedback steps.

#guard minCost [[1, 2, 3], [4, 8, 2], [1, 5, 3]] 2 2 = 8
#guard minCost [[2, 3, 4], [5, 9, 3], [2, 6, 4]] 2 2 = 12
#guard minCost [[3, 4, 5], [6, 10, 4], [3, 7, 5]] 2 2 = 16

-- Prompt 2: Write a function to find the shared elements from the given two lists.

-- Code 2:
def similarElements {α : Type} [BEq α] [Hashable α]
    (xs ys : List α) : HashSet α :=
  let sx : HashSet α := HashSet.ofList xs
  let sy : HashSet α := HashSet.ofList ys
  if sx.size ≤ sy.size then
    -- iterate over the smaller set to minimize work
    sx.fold (init := ({} : HashSet α)) (fun acc x =>
      if sy.contains x then acc.insert x else acc)
  else
    sy.fold (init := ({} : HashSet α)) (fun acc y =>
      if sx.contains y then acc.insert y else acc)

#guard similarElements [3, 4, 5, 6] [5, 7, 4, 10] == HashSet.ofList [4, 5]
#guard similarElements [1, 2, 3, 4] [5, 4, 3, 7]  == HashSet.ofList [3, 4]
#guard similarElements [11, 12, 14, 13] [17, 15, 14, 13] == HashSet.ofList [13, 14]

-- No feedback step needed.

-- Prompt 3: Write a Lean function to identify non-prime numbers.

-- Code 3:
def isPrime (n : Nat) : Bool :=
  if n < 2 then
    false
  else
    -- loop d k: try divisors d, d+1, … ; k is a decreasing fuel
    let rec loop (d k : Nat) : Bool :=
      match k with
      | 0      => true                             -- fuel exhausted; in practice d*d > n already
      | k+1    =>
        if d * d > n then true                     -- no divisor ≤ √n
        else if n % d = 0 then false               -- found a divisor
        else loop (d + 1) k                        -- try next d, decrease fuel
    loop 2 n

def isNonPrime (n : Nat) : Bool :=
  ! isPrime n

-- One feedback step required.

#guard isNonPrime 2 == false
#guard isNonPrime 10 == true
#guard isNonPrime 35 == true
#guard isNonPrime 37 == false

-- Prompt 4: Write a function to find the largest integers from a given list of numbers using heap queue algorithm

-- Code 4:
/-- Merge two descending lists, but return only the first `k` elements. -/
def mergeTakeKDesc : List Int → List Int → Nat → List Int
| _, _, 0 => []
| [], ys, k => ys.take k
| xs, [], k => xs.take k
| x :: xt, y :: yt, k+1 =>
  if x ≥ y then
    x :: mergeTakeKDesc xt (y :: yt) k
  else
    y :: mergeTakeKDesc (x :: xt) yt k

/-- Insert `x` into a descending "heap" (really the current top-k list),
    keeping it sorted and capped at length `k` in O(k). -/
def insertHeap (x : Int) (heap : List Int) (k : Nat) : List Int :=
  mergeTakeKDesc [x] heap k

/-- Top `k` largest elements of `xs`, in descending order, in O(|xs|·k). -/
def kLargest (xs : List Int) (k : Nat) : List Int :=
  xs.foldl (fun heap x => insertHeap x heap k) []

-- No feedback required.

#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 3 == [85, 75, 65]
#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 2 == [85, 75]
#guard kLargest [25, 35, 22, 85, 14, 65, 75, 22, 58] 5 == [85, 75, 65, 58, 35]


-- Prompt 5: Write a function to find the number of ways to fill it with 2 x 1 dominoes for the given 3 x n board.

-- Code 5:
/-- 2×2 integer matrix as (a,b,c,d) ≡ [[a,b],[c,d]]. -/
abbrev Mat := (Int × Int × Int × Int)

@[inline] def matMul (A B : Mat) : Mat :=
  let (a, b, c, d) := A
  let (e, f, g, h) := B
  (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)

@[inline] def matId : Mat := (1, 0, 0, 1)

/-- Binary exponentiation with a structural `fuel`. -/
def matPow (base : Mat) (e : Nat) : Mat :=
  let rec loop (fuel : Nat) (b acc : Mat) (x : Nat) : Mat :=
    match fuel with
    | 0        => acc
    | fuel+1   =>
      match x with
      | 0      => acc
      | x+1    =>
        let acc' := if (x+1) % 2 = 1 then matMul acc b else acc
        -- FIX: recurse on ⌊(x+1)/2⌋, not x/2
        loop fuel (matMul b b) acc' ((x+1) / 2)
  loop (e + 1) base matId e

@[inline] def matMulVec (M : Mat) (v : Int × Int) : Int × Int :=
  let (a, b, c, d) := M
  let (x, y) := v
  (a*x + b*y, c*x + d*y)

/-- Number of domino tilings of a 3×n board.  Runs in O(log n). -/
def tilings3xN (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | _ =>
    if n % 2 = 1 then 0
    else
      let m := n / 2
      if m = 0 then 1 else
      -- b(m) = 4 b(m-1) - b(m-2),  b(0)=1, b(1)=3
      -- T = [[4, -1], [1, 0]]
      let T : Mat := (4, (-1), 1, 0)
      let P := matPow T (m - 1)
      let (bm, _) := matMulVec P (3, 1)
      Int.toNat bm

-- Two feedback steps (including one for a test which did not pass (last one)).

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

-- GPT-5 says it is already optimal

-- Prompt 7: Write a function to find all words which are at least 4 characters long in a string. Words are formed by consecutive characters separated by spaces.

-- Code 7:
/-- Keep words (space-separated) of length ≥ 4, skipping multiple spaces, in one pass. -/
def wordsAtLeast4 (s : String) : List String :=
  let rec go (cs : List Char) (curr : List Char) (clen : Nat) (acc : List String) : List String :=
    match cs with
    | [] =>
        -- end: emit current word if long enough, then reverse accumulated result
        let acc := if clen ≥ 4 then (String.mk curr.reverse) :: acc else acc
        acc.reverse
    | c :: cs' =>
        if c = ' ' then
          -- word boundary: emit only if len ≥ 4; reset buffer
          let acc := if clen ≥ 4 then (String.mk curr.reverse) :: acc else acc
          go cs' [] 0 acc
        else
          -- keep building current word (store reversed for O(1) cons)
          go cs' (c :: curr) (clen + 1) acc
  go s.data [] 0 []

-- Not feedback loop required.

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

-- Already optimal.

-- Prompt 9: Write a Lean function to find the minimum number of rotations required to get the same string.

-- Code 9:
/-- Integer square root: greatest r with r*r ≤ n. -/
def natSqrt (n : Nat) : Nat :=
  if n ≤ 1 then n else
  let rec go (low high : Nat) : Nat :=
    if high ≤ low then low else
      let mid := (low + high + 1) / 2
      if mid * mid ≤ n then go mid high else go low (mid - 1)
  go 1 n

/-- Enumerate all positive divisors of `n` in ascending order. -/
def divisorsAsc (n : Nat) : List Nat :=
  if n = 0 then [] else
  let sqrt := natSqrt n
  let rec loop (d : Nat) (small large : List Nat) : List Nat :=
    if d = 0 then small ++ large
    else
      if n % d = 0 then
        let q := n / d
        if d = q then loop (d - 1) (d :: small) large
        else loop (d - 1) (d :: small) (q :: large)
      else loop (d - 1) small large
  loop sqrt [] []

/-- Split off exactly `k` items; returns (prefix, suffix). -/
def takeK {α} : List α → Nat → (List α × List α)
| xs, 0      => ([], xs)
| [], _      => ([], [])
| x :: xs, k + 1 =>
  let (p, r) := takeK xs k
  (x :: p, r)

/-- Check whether `xs` is a repetition of the finite pattern `pat`.
    Always consumes one input element per step ⇒ structural recursion. -/
def isRepeatOf {α} [DecidableEq α] (xs pat : List α) : Bool :=
  match pat with
  | [] => xs = []
  | p0 :: prest =>
    let rec go (ys : List α) (cur : List α) : Bool :=
      match ys, cur with
      | [], _               => true
      | y :: ys', []        =>                  -- restart pattern at its first symbol
          if y = p0 then go ys' prest else false
      | y :: ys', z :: zs   =>
          if y = z then go ys' zs else false
    go xs (p0 :: prest)

/-- Minimal positive rotation that returns `s` to itself (its minimal period).
    Complexity: O(n · τ(n)). -/
def minRotationsToOriginal (s : String) : Nat :=
  let cs := s.data
  let n  := cs.length
  if n = 0 then 0 else
    let rec tryDivs : List Nat → Nat
    | []        => n
    | d :: ds   =>
        if d = n then n
        else
          let (pat, _) := takeK cs d
          if isRepeatOf cs pat then d else tryDivs ds
    tryDivs (divisorsAsc n)

/-- Left-rotate a list by `k` (single pass; for completeness). -/
def rotateLeftChars (cs : List Char) (k : Nat) : List Char :=
  let n := cs.length
  if n = 0 then cs
  else
    let k' := k % n
    let (front, back) := takeK cs k'
    back ++ front


-- Fixed in five feedback steps (three because two tests did not pass).

#guard minRotationsToOriginal "aaaa" == 1
#guard minRotationsToOriginal "ab" == 2
#guard minRotationsToOriginal "abc" == 3


-- Prompt 10: Write a function to get the n smallest items from a dataset.

-- Code 10:
def kSmallest [Ord α] (xs : List α) (k : Nat) : List α :=
  if k = 0 then
    []
  else
    -- boolean strict order from `compare`
    let lt (a b : α) : Bool := compare a b == Ordering.lt

    -- insert `x` into a descending list according to `lt` (largest at head)
    let rec insertDesc (x : α) : List α → List α
      | []        => [x]
      | y :: ys   =>
        if lt y x then           -- y < x => x should come before y (to keep descending order)
          x :: y :: ys
        else
          y :: insertDesc x ys

    -- keep a descending list of at most k elements = the k smallest seen so far
    let step (acc : List α) (x : α) : List α :=
      if acc.length < k then
        insertDesc x acc
      else
        match acc with
        | [] => []  -- unreachable because length < k was false
        | y :: _ =>
          -- `y` is the current maximum among the kept k elements (since list is descending)
          if lt x y then
            -- x < y: insert x, then drop the (new) head which is still the maximum
            match insertDesc x acc with
            | _ :: ys' => ys'
            | []       => []  -- unreachable
          else
            -- x ≥ y: x is not among the k smallest; ignore it
            acc

    -- fold over all elements and finally return them in ascending order
    (xs.foldl step []).reverse

def nSmallestInts (xs : List Int) (n : Nat) : List Int :=
  kSmallest xs n

-- Not feedback required.

#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 2 == [10,20]
#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 5 == [10,20,20,40,50]
#guard nSmallestInts [10, 20, 50, 70, 90, 20, 50, 40, 60, 80, 100] 3 == [10,20,20]
