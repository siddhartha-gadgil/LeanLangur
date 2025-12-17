import LeanLangur.People
import Mathlib

variable {α β : Type}[LinearOrder α]

def smallestBy (size: β → α)(l: List β)
   (h: l ≠ []) : β :=
  sorry

def youngest (l: List Person)
   (h: l ≠ []) : Person :=
  smallestBy (fun p => p.age) l h
/-!
### Exercises
Prove that `youngest` indeed returns a person from the list who is the youngest.
-/
