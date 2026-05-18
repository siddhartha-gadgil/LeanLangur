import Mathlib.Data.List.Basic -- imports definitions and theorems used below
import Mathlib.Tactic -- imports definitions and theorems used below
import LeanLangur.Basic -- imports definitions and theorems used below
import LeanLangur.Sorted -- imports definitions and theorems used below
/-!
## Prerequisite files

* `Sorted.lean` - sorted-list predicates and equivalent characterizations of sortedness.

## Main concepts introduced

* quicksort.
* termination arguments.
* sortedness proofs.
-/

/-!
## Quicksort Algorithm (Pivot from Head)

Quicksort is a divide-and-conquer sorting algorithm known for its efficiency. It works by recursively partitioning the list around a chosen element (pivot) and then sorting the sub-lists.

Our implementation of quicksort for lists follows the following steps:

* If the list is empty, return the empty list.
* Otherwise, let `pivot` be the first element (`head`) of the list.
* Let `smaller` be the list of elements smaller (`≤`) than `pivot` and `larger` be the list of elements larger (`>`) than `pivot`.
* Recursively sort `smaller` and `larger` lists and concatenate them with `pivot` in between.

We begin by defining `smaller` and `larger` lists. We define them as abbreviations so that they are automatically unfolded by Lean.
-/
namespace langur -- starts a namespace to group the tutorial definitions
variable {α : Type}[LinearOrder α]

/--
Returns a sublist of elements from `l` that are less than or equal to the `pivot`.
-/
@[grind, simp] -- annotation controlling elaboration, simplification, or automation
def smaller (pivot : α) (l : List α) : List α := -- defines `smaller`
  l.filter (fun x => x ≤  pivot) -- maps this case or syntax pattern to its result

/--
Returns a sublist of elements from `l` that are strictly greater than the `pivot`.
-/
@[grind, simp] -- annotation controlling elaboration, simplification, or automation
def larger (pivot : α) (l : List α) : List α := -- defines `larger`
  l.filter (fun x => pivot < x) -- maps this case or syntax pattern to its result

/--
A partial (non-terminating) implementation of Quicksort.
-/
partial def naiveQuickSort : List α → List α -- defines the partial function `naiveQuickSort`
  | [] => [] -- matches the empty list and returns the empty list
  | pivot :: l => -- matches a nonempty list and returns the recursively sorted parts around the pivot
    (naiveQuickSort (smaller pivot l)) ++
    pivot :: (naiveQuickSort (larger pivot l))

/--
The verified implementation of Quicksort for lists.
Terminates because the filtered sublists are strictly smaller than the original list.
-/
def quickSort : List α → List α -- defines `quickSort`
  | [] => [] -- matches the empty list and returns the empty list
  | pivot :: l => -- matches a nonempty list and returns the recursively sorted parts around the pivot
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l))
termination_by l => l.length -- tells Lean which expression decreases for termination


/--
Quicksort of an empty list is an empty list.
-/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem quickSort_nil : quickSort ([] : List α) = [] := by -- starts tactic mode for theorem `quickSort_nil`; the following tactics prove the stated goal
  simp [quickSort] -- simplifies the current goal or hypotheses

/--
Recursive step of the Quicksort implementation.
-/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem quickSort_cons (pivot : α) (l : List α) : -- states and proves theorem `quickSort_cons`
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by -- starts tactic mode; the following tactics prove the proposition just stated
  simp [quickSort] -- simplifies the current goal or hypotheses

/--
An element is in the original list if and only if it is in the `smaller` or `larger` sublists
(when partitioning around a pivot).
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem mem_iff_below_or_above_pivot (pivot : α) -- states and proves theorem `mem_iff_below_or_above_pivot`
  (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by grind -- starts tactic mode and asks `grind` to solve the stated goal automatically

/--
The `quickSort` function preserves the elements of the list.
-/
@[grind =_] -- annotation controlling elaboration, simplification, or automation
theorem mem_iff_mem_quickSort (l: List α)(x : α) : -- states and proves theorem `mem_iff_mem_quickSort`
    x ∈ l ↔ x ∈ quickSort l := by -- starts tactic mode; the following tactics prove the proposition just stated
  fun_induction quickSort <;> grind -- follows the recursive equations of `quickSort` and lets `grind` solve each generated case

section Count
/-!
## Exercises

Prove that quickSort preserves the count of each element. A useful lemma was not annotated with `grind` so this is done below.
-/
attribute [grind .] List.count_eq_zero_of_not_mem


/--
The count of an element in a list is the sum of its counts in the partitioned sublists.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem count_sum_above_below_pivot (pivot : α) -- states and proves theorem `count_sum_above_below_pivot`
  (l : List α)(x : α) :
    (l.count x) = (smaller pivot l).count x +
      (larger pivot l).count x  := by
  sorry

/--
The `quickSort` function preserves the count of each element in the list.
-/
theorem count_eq_count_quickSort (l : List α) -- states and proves theorem `count_eq_count_quickSort`
  (x : α) :
    l.count x = (quickSort l).count x := by -- starts tactic mode; the following tactics prove the proposition just stated
  sorry
end Count -- closes the current namespace or section


/--
Concatenating two sorted lists with a pivot in between results in a sorted list,
provided the pivot respects the bounds of both lists.
-/
theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁) -- states and proves theorem `sorted_sandwitch`
    (l₂ : List α) (h₂ : Sorted l₂)
    (bound : α)
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound)
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) :
    Sorted (l₁ ++ bound :: l₂) := by -- starts tactic mode; the following tactics prove the proposition just stated
    induction h₁ with
    | nil => grind -- matches the empty list and asks `grind` to solve this case
    | singleton x => -- matches a sorted singleton list proof and proves this case with the tactic steps below
      grind [Sorted.step] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal
    | step x y l hxy tail_sorted ih => -- matches a sorted list built from a head and sorted tail and proves this case with the tactic steps below
      grind [Sorted.step] -- uses `grind` with the listed lemmas unfolded or available to close the remaining goal

/--
The `quickSort` function correctly sorts any input list.
-/
theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by -- starts tactic mode for theorem `quickSort_sorted`; the following tactics prove the stated goal
  cases l with -- splits or inverts `l with`, creating one goal for each possible constructor
  | nil => -- matches the empty list and proves this case with the tactic steps below
    simp [quickSort_nil] -- simplifies the current goal or hypotheses
    apply Sorted.nil -- applies `Sorted.nil` backwards, replacing the current goal by its premises
  | cons pivot l => -- matches a nonempty list and proves this case with the tactic steps below
    rw [quickSort_cons]
    have h_small := -- records an intermediate fact for the proof
      quickSort_sorted (smaller pivot l)
    have h_large := -- records an intermediate fact for the proof
      quickSort_sorted (larger pivot l)
    apply sorted_sandwitch <;> grind -- applies `sorted_sandwitch <;> grind` backwards, replacing the current goal by its premises
termination_by l.length -- tells Lean which expression decreases for termination
/-!
## Next files

* None in the README dependency diagram.
-/
