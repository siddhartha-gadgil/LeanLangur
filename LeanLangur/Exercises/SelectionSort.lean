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
  match l with
  | [x] => simp [smallest]
  | x :: y :: xs =>
    have ih := smallest_mem (y :: xs) (by simp)
    grind [smallest]

@[grind .]
theorem smallest_le_all (l: List α) (h: l ≠ []) (x: α) :
  x ∈ l → smallest l h ≤ x := by
  match l with
  | [y] =>
    grind [smallest]
  | y :: z :: xs =>
    have ih :=
      smallest_le_all (z :: xs) (by simp) x
    grind [smallest]

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
  apply Iff.intro
  match l with
  | [] => grind
  | head ::tail =>
    simp [selectionSort]
    if p:x = smallest (head :: tail) (by simp) then
      grind
    else
      have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length < (head :: tail).length := by grind
      have ih := mem_iff_mem_selectionSort ((head ::tail).erase (smallest (head :: tail) (by simp))) x
      grind
  · match l with
  | [] => grind
  | head :: tail =>
    have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length < (head :: tail).length := by grind
    have ih := mem_iff_mem_selectionSort ((head ::tail).erase (smallest (head :: tail) (by simp))) x
    grind
termination_by l.length

theorem selectionSort_sorted (l : List α) :
  Sorted (selectionSort l) := by
  match l with
  | [] => grind [Sorted.nil]
  | head :: tail =>
    have : ((head ::tail).erase (smallest (head :: tail) (by simp))).length < (head :: tail).length := by grind
    have ih := selectionSort_sorted ((head ::tail).erase (smallest (head :: tail) (by simp)))
    grind
termination_by l.length
