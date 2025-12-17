import Mathlib.Data.List.Basic
import Mathlib.Tactic

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

variable {α : Type}[LinearOrder α]

@[grind, simp]
def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

@[grind, simp]
def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => pivot < x)

def quickSort : List α → List α
  | [] => []
  | pivot :: l =>
    have hs : (smaller pivot l).length < (pivot :: l).length := by
      grind
    have hl : (larger pivot l).length < (pivot :: l).length := by
      grind
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l))
termination_by l => l.length


@[simp, grind .]
theorem quickSort_nil : quickSort ([] : List α) = [] := by
  simp [quickSort]

@[simp, grind .]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by
  simp [quickSort]

@[grind .]
theorem mem_iff_below_or_above_pivot (pivot : α)
  (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by grind

@[grind =_]
theorem mem_iff_mem_quickSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ quickSort l := by
  cases l with
  | nil => simp
  | cons pivot l =>
    have : (smaller pivot l).length < (pivot :: l).length := by
      grind
    have : (larger pivot l).length < (pivot :: l).length := by
      grind
    have ih₁ := mem_iff_mem_quickSort (smaller pivot l)
    have ih₂ := mem_iff_mem_quickSort (larger pivot l)
    grind
termination_by l.length

section Count
/-!
### Exercises

Prove that quickSort preserves the count of each element. A useful lemma was not annotated with `grind` so this is done below.
-/
attribute [grind .] List.count_eq_zero_of_not_mem


@[grind .]
theorem count_sum_above_below_pivot (pivot : α)
  (l : List α)(x : α) :
    (l.count x) = (smaller pivot l).count x +
      (larger pivot l).count x  := by
  sorry

theorem count_eq_count_quickSort (l : List α)
  (x : α) :
    l.count x = (quickSort l).count x := by
  sorry
end Count

section Sorted
inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

@[grind .]
theorem head_le_of_sorted  (a: α) (l : List α) :
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by
  intro h
  match h with
  | Sorted.singleton .. => simp
  | Sorted.step .(a) y l hxy tail_sorted =>
    have ih := head_le_of_sorted y l tail_sorted
    grind

@[grind .]
theorem cons_sorted (l : List α) :  Sorted l → (a : α) →
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by
  intro h₁ a h₀
  match l with
  | [] =>
    apply Sorted.singleton
  | x :: l' =>
    grind [Sorted.step]

theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁)
    (l₂ : List α) (h₂ : Sorted l₂)
    (bound : α)
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound)
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) :
    Sorted (l₁ ++ bound :: l₂) := by
    induction h₁ with
    | nil => grind
    | singleton x =>
      grind [Sorted.step]
    | step x y l hxy tail_sorted ih =>
      grind [Sorted.step]

theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  cases l with
  | nil =>
    simp [quickSort_nil]
    apply Sorted.nil
  | cons pivot l =>
    rw [quickSort_cons]
    have : (smaller pivot l).length < (pivot :: l).length :=
        by grind
    have : (larger pivot l).length < (pivot :: l).length :=
        by grind
    have h_small :=
      quickSort_sorted (smaller pivot l)
    have h_large :=
      quickSort_sorted (larger pivot l)
    apply sorted_sandwitch <;> grind
termination_by l.length


@[grind .]
def monotone (l : List α) : Prop := ∀ i j,
  (h₁: i < j) → (h₂ : j < l.length) →
    l[i]' (by grind) ≤ l[j]' (by grind)

theorem monotone_of_sorted (l : List α)
  (h : Sorted l) : monotone l := by
  induction h with
  | nil => grind
  | singleton x =>
    grind
  | step x y l hxy tail_sorted ih =>
    intro i j h₁ h₂
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j' =>
        trans y <;> grind
    | succ i' =>
      cases j with
      | zero => contradiction
      | succ j' => grind

@[grind .]
theorem tail_monotone_of_monotone {y: α}
  {ys : List α} (h : monotone (y :: ys)) :
  monotone ys := by
  intro i j h₁ h₂
  have h₁' : i + 1 < j + 1 := by
    grind
  have h₂' : j + 1 < (ys.length + 1) := by
    grind
  specialize h (i + 1) (j + 1) h₁' h₂'
  grind

theorem sorted_of_monotone (l : List α)
  (h : monotone l) : Sorted l := by
  induction l with
  | nil => apply Sorted.nil
  | cons x xs ih =>
    cases xs with
    | nil => apply Sorted.singleton
    | cons y ys =>
      apply Sorted.step
      · apply h 0 1 (by simp) (by simp)
      · grind
end Sorted
