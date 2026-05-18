import Mathlib.Order.Lattice -- imports definitions and theorems used below
/-!
## Prerequisite files

* `Adder.lean` - typeclasses, custom `Add` instances, and typeclass inference.

## Main concepts introduced

* programs with proofs.
* nonempty-list algorithms over linear orders.
-/

/-!
## Largest Element in a List: Programs with Proofs

We illustrate how to write programs with proofs in Lean by implementing a function to find the largest element in a (non-empty) list, along with proofs that the element is indeed in the list and is larger than or equal to all other elements.

* We first implement `largestNat` for lists of natural numbers, along with proofs `largestNat_mem` and `largestNat_ge_all`.

* We then generalize this to lists of any type with a linear order, implementing `largest` for *non-empty* lists along with proofs `largest_mem` and `largest_ge_all`.
-/

namespace langur -- starts a namespace to group the tutorial definitions

def largestNat : List Nat → Nat -- defines `largestNat`
| []       => 0  -- placeholder for empty list
| [x]      => x -- matches a singleton list and returns `x`
| x :: y :: xs => -- matches a list with at least two elements and returns `max x (largestNat (y :: xs))`
    max x (largestNat (y :: xs))

#check largestNat.induct -- asks Lean to display the inferred type

#eval largestNat [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 9

theorem largestNat_mem : ∀ (l : List Nat), l ≠ [] → largestNat l ∈ l := by -- starts tactic mode for theorem `largestNat_mem`; the following tactics prove the stated goal
  intro l -- moves leading forall variables or implication hypotheses into the local context
  fun_induction largestNat <;> grind -- follows the recursive equations of `largestNat` and lets `grind` solve each generated case


theorem largestNat_ge_all (l: List Nat) (x: Nat) : -- states and proves theorem `largestNat_ge_all`
  x ∈ l → x ≤ largestNat l := by -- starts tactic mode; the following tactics prove the proposition just stated
  fun_induction largestNat <;> grind -- follows the recursive equations of `largestNat` and lets `grind` solve each generated case

variable {α : Type}[LinearOrder α]

def largest₀ [Inhabited α] (l: List α) : α := -- defines `largest`
  match l with -- splits computation into cases by pattern matching
  | [] => default -- matches the empty list and returns the default value
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: xs => -- matches a list with at least two elements and returns `max x (largest₀ (y :: xs))`
    max x (largest₀ (y :: xs))

example [Inhabited α] : α × α := -- checks an unnamed example or proof
  default

@[grind .] -- annotation controlling elaboration, simplification, or automation
def largest (l: List α) (h: l ≠ []) : α := -- defines `largest`
  match l with -- splits computation into cases by pattern matching
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: xs => -- matches a list with at least two elements and returns `max x (largest (y :: xs) (by simp))`
    max x (largest (y :: xs) (by simp))

#eval largest [1, 3, 2] (by simp)  -- evaluates to 3

theorem largest_mem (l: List α) (h: l ≠ []) : -- states and proves theorem `largest_mem`
  largest l h ∈ l := by -- starts tactic mode; the following tactics prove the proposition just stated
  match l with -- splits computation into cases by pattern matching
  | [x] => grind -- matches a singleton list and asks `grind` to solve this case
  | x :: y :: xs => -- matches a list with at least two elements and proves this case using the following proof steps
    have ih := largest_mem (y :: xs) (by simp) -- records an intermediate fact for the proof
    grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes

theorem largest_ge_all (l: List α) (h: l ≠ []) (x: α) : -- states and proves theorem `largest_ge_all`
  x ∈ l → x ≤ largest l h := by -- starts tactic mode; the following tactics prove the proposition just stated
  match l with -- splits computation into cases by pattern matching
  | [y] => -- matches a singleton list and proves this case with the tactic steps below
    grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes
  | y :: z :: xs => -- matches a list with at least two elements and proves this case using the following proof steps
    have ih := -- records an intermediate fact for the proof
      largest_ge_all (z :: xs) (by simp) x
    grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes

def largest? (l: List α) : Option α := -- defines `largest?`
  match l with -- splits computation into cases by pattern matching
  | [] => none -- matches the empty list and returns `none`
  | x :: ys   => -- matches a nonempty list and inspects `largest? ys` in a nested match to decide the result
    match largest? ys  with -- splits computation into cases by pattern matching
    | none => some x -- matches a missing optional value and returns `some x`
    | some m => some (max x m) -- matches a present optional value and returns `some (max x m)`

#eval largest? [1, 3, 2]  -- evaluates to some 3
#eval largest? ([] : List Nat)  -- evaluates to none

def doubleLargest?₀ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  match largest? l with -- splits computation into cases by pattern matching
  | none => none -- matches a missing optional value and returns `none`
  | some m => some (2 * m) -- matches a present optional value and returns `some (2 * m)`

def doubleLargest?₁ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  (largest? l).map (fun m => 2 * m)

def doubleLargest?₂ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  do -- starts a `do` block for monadic sequencing
    let m ← largest? l -- binds an intermediate value for the following expression
    return 2 * m -- returns this value from the monadic block

def sumLargest? (l1 l2: List Nat) : Option Nat := -- defines `sumLargest?`
  do -- starts a `do` block for monadic sequencing
    let m1 ← largest? l1 -- binds an intermediate value for the following expression
    let m2 ← largest? l2 -- binds an intermediate value for the following expression
    return m1 + m2 -- returns this value from the monadic block

#eval sumLargest? [1, 3, 2] [4, 5, 6]  -- evaluates to some 9

#eval sumLargest? [] [4, 5, 6]  -- evaluates to none

def largestImp (l: List Nat): Nat := Id.run do -- defines `largestImp`
  let mut maxSoFar := 0 -- binds an intermediate value for the following expression
  for x in l do -- iterates through these values in the monadic block
    if x > maxSoFar then -- branches on this decidable condition
      maxSoFar := x
  return maxSoFar -- returns this value from the monadic block

end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
