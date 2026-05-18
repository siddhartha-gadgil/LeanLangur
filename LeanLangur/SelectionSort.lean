import Mathlib -- imports definitions and theorems used below
import LeanLangur.QuickSort -- imports definitions and theorems used below
/-!
## Prerequisite files

* `Sorted.lean` - sorted-list predicates and equivalent characterizations of sortedness.

## Main concepts introduced

* selection sort.
* recursive sorting with correctness proofs.
-/

namespace langur -- starts a namespace to group the tutorial definitions
variable {α : Type}[LinearOrder α]
/-!
We now do the same for smallest.
-/
def smallest (l: List α) (h: l ≠ []) : α := -- defines `smallest`
  match l with -- splits computation into cases by pattern matching
  | [] => by contradiction -- matches the empty list and proves the case by contradiction
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: xs => -- matches a list with at least two elements and returns `min x (smallest (y :: xs) (by simp))`
    min x (smallest (y :: xs) (by simp))

@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem smallest_mem (l: List α) (h: l ≠ []) : -- states and proves theorem `smallest_mem`
  smallest l h ∈ l := by -- starts tactic mode; the following tactics prove the proposition just stated
  match l with -- splits computation into cases by pattern matching
  | [x] => simp [smallest] -- matches a singleton list and simplifies this proof case
  | x :: y :: xs => -- matches a list with at least two elements and proves this case using the following proof steps
    have ih := smallest_mem (y :: xs) (by simp) -- records an intermediate fact for the proof
    grind [smallest] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal

@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem smallest_le_all (l: List α) (h: l ≠ []) (x: α) : -- states and proves theorem `smallest_le_all`
  x ∈ l → smallest l h ≤ x := by -- starts tactic mode; the following tactics prove the proposition just stated
  match l with -- splits computation into cases by pattern matching
  | [y] => -- matches a singleton list and proves this case with the tactic steps below
    grind [smallest] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal
  | y :: z :: xs => -- matches a list with at least two elements and proves this case using the following proof steps
    have ih := -- records an intermediate fact for the proof
      smallest_le_all (z :: xs) (by simp) x
    grind [smallest] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal

/-!
We now implement Selection Sort using smallest.
-/
def selectionSort : List α → List α -- defines `selectionSort`
  | [] => [] -- matches the empty list and returns the empty list
  | x :: ys => -- matches a nonempty list and proves this case using the following proof steps
    let s := smallest (x :: ys) (by simp) -- binds an intermediate value for the following expression
    have : ((x :: ys).erase s).length < (x :: ys).length := by grind -- records an intermediate fact for the proof
    have : ((x :: ys).erase (smallest (x :: ys) (by simp))).length ≤ ys.length := by -- records an intermediate fact for the proof
      grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes
    s :: selectionSort ((x :: ys).erase s)
termination_by l => l.length -- tells Lean which expression decreases for termination

@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem mem_iff_mem_selectionSort (l: List α)(x : α) : -- states and proves theorem `mem_iff_mem_selectionSort`
    x ∈ l ↔ x ∈ selectionSort l := by -- starts tactic mode; the following tactics prove the proposition just stated
  apply Iff.intro -- applies `Iff.intro` backwards, replacing the current goal by its premises
  match l with -- splits computation into cases by pattern matching
  | [] => grind -- matches the empty list and asks `grind` to solve this case
  | head ::tail => -- matches `head ::tail` and proves this case with the tactic steps below
    simp [selectionSort] -- simplifies the current goal or hypotheses
    if p:x = smallest (head :: tail) (by simp) then -- branches on this decidable condition
      grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes
    else -- handles the alternative branch
      have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length ≤  tail.length := by grind -- records an intermediate fact for the proof
      have ih := mem_iff_mem_selectionSort ((head ::tail).erase (smallest (head :: tail) (by simp))) x -- records an intermediate fact for the proof
      grind -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes
  · match l with -- focuses the next proof branch
  | [] => grind [selectionSort] -- matches the empty list and asks `grind` to solve this case
  | head :: tail => -- matches a nonempty list and proves this case using the following proof steps
    have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length ≤ tail.length := by grind -- records an intermediate fact for the proof
    have ih := mem_iff_mem_selectionSort ((head ::tail).erase (smallest (head :: tail) (by simp))) x -- records an intermediate fact for the proof
    grind [selectionSort] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal
termination_by l.length -- tells Lean which expression decreases for termination

theorem selectionSort_sorted (l : List α) : -- states and proves theorem `selectionSort_sorted`
  Sorted (selectionSort l) := by -- starts tactic mode; the following tactics prove the proposition just stated
  match l with -- splits computation into cases by pattern matching
  | [] => grind [selectionSort, Sorted.nil] -- matches the empty list and asks `grind` to solve this case
  | head :: tail => -- matches a nonempty list and proves this case using the following proof steps
    have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length ≤ tail.length := by grind -- records an intermediate fact for the proof
    have ih := selectionSort_sorted ((head ::tail).erase (smallest (head :: tail) (by simp))) -- records an intermediate fact for the proof
    grind [selectionSort] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal
termination_by l.length -- tells Lean which expression decreases for termination
end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
