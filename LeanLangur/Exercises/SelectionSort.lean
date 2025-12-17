import Mathlib
import LeanLangur.QuickSort

/-!
## Exercise: Selection Sort

In this exercise, we implement Selection Sort using a helper function `smallest` that finds the smallest element in a non-empty list. We then prove that Selection Sort preserves membership and that the resulting list is sorted.

The theorems you need to prove are marked with `sorry` as placeholders.
-/

variable {α : Type}[LinearOrder α]
/-!
We now do the same for smallest.
-/
def smallest (l: List α) (h: l ≠ []) : α :=
  match l with
  | [] => by contradiction
  | [x] => x
  | x :: y :: xs =>
    min x (smallest (y :: xs) (by simp))

@[grind .]
theorem smallest_mem (l: List α) (h: l ≠ []) :
    smallest l h ∈ l := by
  sorry

@[grind .]
theorem smallest_le_all (l: List α)
    (h: l ≠ []) (x: α) :
    x ∈ l → smallest l h ≤ x := by
  sorry

/-!
We now implement Selection Sort using smallest.
-/
@[grind .]
def selectionSort : List α → List α
  | [] => []
  | x :: ys =>
    let s := smallest (x :: ys) (by simp)
    have : ((x :: ys).erase s).length < (x :: ys).length := by grind
    s :: selectionSort ((x :: ys).erase s)
termination_by l => l.length

@[grind .]
theorem mem_iff_mem_selectionSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ selectionSort l := by
  sorry

theorem selectionSort_sorted (l : List α) :
    Sorted (selectionSort l) := by
  sorry
