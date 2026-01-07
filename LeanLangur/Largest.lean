import Mathlib.Order.Lattice
/-!
## Largest Element in a List: Programs with Proofs

We illustrate how to write programs with proofs in Lean by implementing a function to find the largest element in a (non-empty) list, along with proofs that the element is indeed in the list and is larger than or equal to all other elements.

* We first implement `largestNat` for lists of natural numbers, along with proofs `largestNat_mem` and `largestNat_ge_all`.

* We then generalize this to lists of any type with a linear order, implementing `largest` for *non-empty* lists along with proofs `largest_mem` and `largest_ge_all`.
-/
def largestNat : List Nat → Nat
| []       => 0  -- placeholder for empty list
| [x]      => x
| x :: y :: xs =>
    max x (largestNat (y :: xs))

#check largestNat.induct

#eval largestNat [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 9

theorem largestNat_mem : ∀ (l : List Nat), l ≠ [] → largestNat l ∈ l := by
  intro l
  fun_induction largestNat <;> grind

-- | [], h => by
--   simp at h
-- | [x], h => by simp [largestNat]
-- | x :: y :: xs, h =>
--     by
--       have ih :=
--         largestNat_mem (y :: xs) (by simp)
--       grind [largestNat]

theorem largestNat_ge_all (l: List Nat) (h: l ≠ []) (x: Nat) :
  x ∈ l → x ≤ largestNat l := by
  fun_induction largestNat <;> grind
  -- match l with
  -- | [y] =>
  --   grind [largestNat]
  -- | y :: z :: xs =>
  --   have ih :=
  --     largestNat_ge_all (z :: xs) (by simp) x
  --   grind [largestNat]

variable {α : Type}[LinearOrder α]

def largest₀ [Inhabited α] (l: List α) : α :=
  match l with
  | [] => default
  | [x] => x
  | x :: y :: xs =>
    max x (largest₀ (y :: xs))

example [Inhabited α] : α × α :=
  default

@[grind .]
def largest (l: List α) (h: l ≠ []) : α :=
  match l with
  | [x] => x
  | x :: y :: xs =>
    max x (largest (y :: xs) (by simp))

#eval largest [1, 3, 2] (by simp)  -- evaluates to 3

theorem largest_mem (l: List α) (h: l ≠ []) :
  largest l h ∈ l := by
  match l with
  | [x] => grind
  | x :: y :: xs =>
    have ih := largest_mem (y :: xs) (by simp)
    grind

theorem largest_ge_all (l: List α) (h: l ≠ []) (x: α) :
  x ∈ l → x ≤ largest l h := by
  match l with
  | [y] =>
    grind
  | y :: z :: xs =>
    have ih :=
      largest_ge_all (z :: xs) (by simp) x
    grind

def largest? (l: List α) : Option α :=
  match l with
  | [] => none
  | x :: ys   =>
    match largest? ys  with
    | none => some x
    | some m => some (max x m)

#eval largest? [1, 3, 2]  -- evaluates to some 3
#eval largest? ([] : List Nat)  -- evaluates to none

def doubleLargest?₀ (l: List Nat) : Option Nat  :=
  match largest? l with
  | none => none
  | some m => some (2 * m)

def doubleLargest?₁ (l: List Nat) : Option Nat  :=
  (largest? l).map (fun m => 2 * m)

def doubleLargest?₂ (l: List Nat) : Option Nat  :=
  do
    let m ← largest? l
    return 2 * m

def sumLargest? (l1 l2: List Nat) : Option Nat :=
  do
    let m1 ← largest? l1
    let m2 ← largest? l2
    return m1 + m2

#eval sumLargest? [1, 3, 2] [4, 5, 6]  -- evaluates to some 9

#eval sumLargest? [] [4, 5, 6]  -- evaluates to none

def largestImp (l: List Nat): Nat := Id.run do
  let mut maxSoFar := 0
  for x in l do
    if x > maxSoFar then
      maxSoFar := x
  return maxSoFar
