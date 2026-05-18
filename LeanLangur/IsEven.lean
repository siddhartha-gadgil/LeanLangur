import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* `People.lean` - structures and named fields.
* `BinTree.lean` - inductive types, recursive functions on trees, and membership proofs.

## Main concepts introduced

* inductive propositions.
* basic use of `grind`.
-/

/-!
# Even Natural Numbers

This module defines the property of being an even natural number using an inductive predicate
and provides several proofs about even numbers.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
Inductive predicate for even natural numbers.
* `0` is even.
* If `n` is even, then `n + 2` is even.
-/
@[grind cases] -- annotation controlling elaboration, simplification, or automation
inductive IsEven : Nat → Prop -- declares the inductive type or proposition `IsEven`
  | zeroEven : IsEven 0 -- declares another constructor or syntax alternative
  | addTwoEven (h : IsEven n) : IsEven (n + 2) -- declares another constructor or syntax alternative

open IsEven -- opens names so constructors or helpers can be written unqualified

/--
Zero is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem zero_even : IsEven 0 := by -- starts tactic mode for theorem `zero_even`; the following tactics prove the stated goal
  apply zeroEven -- applies `zeroEven` backwards, replacing the current goal by its premises

/--
If `n` is even, then `n + 2` is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem addTwo_even (n: Nat) (h: IsEven n) : -- states and proves theorem `addTwo_even`
  IsEven (n + 2) := by -- starts tactic mode; the following tactics prove the proposition just stated
    apply addTwoEven -- applies `addTwoEven` backwards, replacing the current goal by its premises
    assumption -- solves the goal from an existing hypothesis

/--
Twice any natural number is even.
-/
theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by -- starts tactic mode for theorem `IsEven_two_mul`; the following tactics prove the stated goal
  induction n <;> grind -- performs induction on `n` and sends each base/step goal to `grind`

/--
The successor of an even number is not even (i.e., it is odd).
-/
theorem succ_odd_of_isEven {n : Nat} -- states and proves theorem `succ_odd_of_isEven`
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction h <;> grind -- performs induction on `h` and sends each base/step goal to `grind`

/--
For any natural number `n`, either `n` is even or `n + 1` is even.
-/
theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1) -- states and proves theorem `nOrSuccNeven`
  := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction n <;> grind -- performs induction on `n` and sends each base/step goal to `grind`

/-!
## Exercise: Odd numbers

Define an inductive predicate `IsOdd : Nat → Prop` for odd natural numbers, and prove that any natural number is either even or odd, but not both (As two separate propositions).
-/
end langur -- closes the current namespace or section
/-!
## Next files

* `Sorted.lean` - sorted-list predicates; equivalent characterizations of sortedness.
* `NonAtom.lean` - constructing typeclasses; typeclass fields and instances.
* `Smallest.lean` - generic smallest-element functions; linear-order typeclass parameters.
* `Eratosthenes.lean` - prime numbers; the Sieve of Eratosthenes exercise.
-/
