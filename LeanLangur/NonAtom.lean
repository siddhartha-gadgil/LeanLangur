/-!
## Prerequisite files

* `IsEven.lean` - inductive propositions and basic use of `grind`.

## Main concepts introduced

* constructing typeclasses.
* typeclass fields and instances.
-/

/-!
# NonAtom Typeclass

This module defines the `NonAtom` typeclass, which identifies types that have at least
two distinct elements. It provides instances for several common types like `Nat`, `Bool`,
`List`, `Option`, and products.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
A typeclass for types that have at least two distinct elements.
-/
class NonAtom (α : Type) where -- declares the typeclass `NonAtom`
    /-- The first distinct element. -/
    firstAtom : α
    /-- The second distinct element. -/
    secondAtom : α
    /-- Proof that the two elements are distinct. -/
    firstNeqSecond : firstAtom ≠ secondAtom

/--
Helper function to get the first atom of a `NonAtom` type.
-/
def firstAtom (α : Type) [c: NonAtom α] : α := c.firstAtom -- defines `firstAtom`

/--
Helper function to get the second atom of a `NonAtom` type.
-/
def secondAtom (α : Type) [c: NonAtom α] : α := c.secondAtom -- defines `secondAtom`

/--
Theorem stating that the two atoms of a `NonAtom` type are distinct.
-/
theorem firstAtomNeqSecond (α : Type) [c: NonAtom α] : firstAtom α  ≠ secondAtom α := c.firstNeqSecond -- states and proves theorem `firstAtomNeqSecond`

/-- `Nat` is a `NonAtom` type with 0 and 1. -/
instance : NonAtom Nat where -- provides an instance for typeclass search
    firstAtom := 0
    secondAtom := 1
    firstNeqSecond := by decide -- proves the inequality by computation with decidable equality

/-- `Bool` is a `NonAtom` type with false and true. -/
instance: NonAtom Bool where -- provides an instance for typeclass search
    firstAtom := false
    secondAtom := true
    firstNeqSecond := by decide -- proves the inequality by computation with decidable equality

/-- If `α` is `NonAtom`, then `List α` is also `NonAtom` (empty list vs single-element list). -/
instance [NonAtom α] : NonAtom (List α) where -- provides an instance for typeclass search
    firstAtom := []
    secondAtom := [firstAtom α]
    firstNeqSecond := by simp -- proves the field by simplifying the two constructors or expressions

/-- If `α` is `Inhabited`, then `Option α` is `NonAtom` (none vs some). -/
instance [Inhabited α] : NonAtom (Option α) where -- provides an instance for typeclass search
    firstAtom := none
    secondAtom := some (default : α)
    firstNeqSecond := by simp -- proves the field by simplifying the two constructors or expressions

/-- If `α` is `NonAtom`, then `α × α` is also `NonAtom`. -/
instance [NonAtom α] : NonAtom (α × α) where -- provides an instance for typeclass search
    firstAtom := (firstAtom α, firstAtom α)
    secondAtom := (secondAtom α, secondAtom α)
    firstNeqSecond := by simp [firstAtomNeqSecond α] -- proves the field by simplifying the two constructors or expressions

/-- A `NonAtom` type is always `Inhabited` (using `firstAtom`). -/
instance [NonAtom α] : Inhabited α where -- provides an instance for typeclass search
    default := firstAtom α

/-- If `α` is `NonAtom` and `β` is `Inhabited`, then `α × β` is `NonAtom`. -/
instance [NonAtom α] [Inhabited β] : NonAtom (α × β) where -- provides an instance for typeclass search
    firstAtom := (firstAtom α, (default : β))
    secondAtom := (secondAtom α, (default : β))
    firstNeqSecond := by simp [firstAtomNeqSecond α] -- proves the field by simplifying the two constructors or expressions

/-- If `α` is `Inhabited` and `β` is `NonAtom`, then `α × β` is `NonAtom`. -/
instance [Inhabited α] [NonAtom β] : NonAtom (α × β) where -- provides an instance for typeclass search
    firstAtom := ((default : α), firstAtom β)
    secondAtom := ((default : α), secondAtom β)
    firstNeqSecond := by simp [firstAtomNeqSecond β] -- proves the field by simplifying the two constructors or expressions

#eval firstAtom (Nat × Unit) -- runs this expression as a tutorial check

#eval secondAtom <| Nat × Nat -- runs this expression as a tutorial check

end langur -- closes the current namespace or section
/-!
## Next files

* `TryInterpret.lean` - frontend interpretation; environment manipulation; generated Lean snippets.
-/
