import LeanLangur.People
import Mathlib

variable {α β : Type}[LinearOrder α]

@[grind .]
def smallestBy (size: β → α)(l: List β)
   (h: l ≠ []) : β := match l with
  | [x] => x
  | x :: y :: xs =>
    let s := smallestBy size (y :: xs) (by simp)
    if size x ≤ size s then x else s

def youngest (l: List Person)
   (h: l ≠ []) : Person :=
  smallestBy (fun p => p.age) l h
/-!
### Exercises
Prove that `youngest` indeed returns a person from the list who is the youngest.
-/
theorem smallestBy_mem (size: β → α)(l: List β)
   (h: l ≠ []) :
   smallestBy size l h ∈ l := by
  sorry

theorem smallestBy_le_all (size: β → α)
   (l: List β)(h: l ≠ []) (x: β) :
   x ∈ l → size (smallestBy size l h) ≤ size x := by
match l with
  | [x] => grind
  | a :: b :: xs =>
    have ih :=
      smallestBy_le_all size (b :: xs) (by simp) x
    let s := smallestBy size (b :: xs) (by simp)
    if p : size x ≤ size s then
      grind
    else
      grind

theorem zero_not_succ (n : Nat) :
  0 ≠ Nat.succ n := by
  intro h
  cases h

#check Nat.rec
