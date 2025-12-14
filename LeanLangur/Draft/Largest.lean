import Mathlib.Order.Lattice

def largestNat (l: List Nat)  : Nat :=
  match l with
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
    Nat.max x (largestNat (y :: xs))

theorem largestNat_mem (l: List Nat) (h: l ≠ []) :
  largestNat l ∈ l := by
  match l with
  | [x] => simp [largestNat]
  | x :: y :: xs =>
    have ih := largestNat_mem (y :: xs) (by simp)
    grind [largestNat]

theorem largestNat_ge_all (l: List Nat) (h: l ≠ []) (x: Nat) :
  x ∈ l → x ≤ largestNat l := by
  match l with
  | [y] =>
    grind [largestNat]
  | y :: z :: xs =>
    have ih :=
      largestNat_ge_all (z :: xs) (by simp) x
    grind [largestNat]

variable {α : Type}[LinearOrder α]

def largest (l: List α) (h: l ≠ []) : α :=
  match l with
  | [] => by contradiction
  | [x] => x
  | x :: y :: xs =>
    max x (largest (y :: xs) (by simp))

theorem largest_mem (l: List α) (h: l ≠ []) :
  largest l h ∈ l := by
  match l with
  | [x] => simp [largest]
  | x :: y :: xs =>
    have ih := largest_mem (y :: xs) (by simp)
    simp [largest]
    by_cases x ≤ largest (y :: xs)
      (by simp) <;> grind

theorem largest_ge_all (l: List α) (h: l ≠ []) (x: α) :
  x ∈ l → x ≤ largest l h := by
  match l with
  | [y] =>
    grind [largest]
  | y :: z :: xs =>
    have ih :=
      largest_ge_all (z :: xs) (by simp) x
    grind [largest]
