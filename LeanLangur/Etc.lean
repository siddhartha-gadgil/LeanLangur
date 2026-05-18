import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* None in the README dependency diagram.

## Main concepts introduced

* custom empty and false types.
* recursion on empty types.
-/

/-!
# Miscellaneous Examples

A collection of various examples in Lean 4, including:
* Custom empty and false types.
* Simple proofs and exercises.

This is stuff added while livecoding as answers to questions, and is not meant to be a cohesive module. It is just a scratchpad for various examples.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
A custom empty type.
-/
inductive MyEmpty where -- declares the inductive type or proposition `MyEmpty`
  deriving Repr -- asks Lean to generate standard instances automatically

/--
A custom false proposition.
-/
inductive MyFalse : Prop where -- declares the inductive type or proposition `MyFalse`

/--
Principle of explosion for the custom empty type.
-/
def ofEmpty{α : Type} : MyEmpty → α -- defines `ofEmpty`
  | e => by cases e -- matches `e` and proves the case by cases e

/--
Principle of explosion for the custom false proposition.
-/
theorem myFalse_elim (f : MyFalse) : ∀ {P : Prop}, P := by -- starts tactic mode for theorem `myFalse_elim`; the following tactics prove the stated goal
  intro P -- moves leading forall variables or implication hypotheses into the local context
  cases f -- splits or inverts `f`, creating one goal for each possible constructor

/--
A very simple proof that `1 ≤ 5`.
-/
theorem easy : 1 ≤ 5 := by -- starts tactic mode for theorem `easy`; the following tactics prove the stated goal
  apply Nat.le_succ_of_le -- applies `Nat.le_succ_of_le` backwards, replacing the current goal by its premises
  apply Nat.le_succ_of_le -- applies `Nat.le_succ_of_le` backwards, replacing the current goal by its premises
  apply Nat.le_succ_of_le -- applies `Nat.le_succ_of_le` backwards, replacing the current goal by its premises
  apply Nat.le_succ_of_le -- applies `Nat.le_succ_of_le` backwards, replacing the current goal by its premises
  apply Nat.le_refl -- applies `Nat.le_refl` backwards, replacing the current goal by its premises

#print easy -- prints Lean's generated declaration for inspection

/--
Predicate for checking if a real number is rational.
-/
def IsRational (x : ℝ) : Prop := -- defines `IsRational`
  ∃ (α  : ℚ), x = α

set_option pp.all true in -- sets an elaborator or diagnostic option for this example
#print IsRational -- prints Lean's generated declaration for inspection

/-- A subtype representing natural numbers that are even. -/
abbrev EvenNat := { n : Nat // n % 2 = 0} -- introduces `EvenNat` as a reducible abbreviation


end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
