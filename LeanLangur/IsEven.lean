import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* `People.lean` - structures and named fields.
* `BinTree.lean` - inductive types, recursive functions on trees, and membership proofs.

## Main concepts introduced

* inductive propositions.
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
inductive IsEven : (n : Nat) → Prop -- declares the inductive type or proposition `IsEven`
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

example : IsEven 4 :=
   IsEven.addTwoEven (@IsEven.addTwoEven 0 IsEven.zeroEven) -- constructs a proof of `IsEven 4` using the constructors of `IsEven`

example : IsEven 24 := by
  repeat (apply IsEven.addTwoEven)
  apply IsEven.zeroEven -- constructs a proof of `IsEven 24` using the constructors of `IsEven`

example : ¬(IsEven 1) :=
  fun h ↦
    nomatch h

example : ¬(IsEven 1) := by
  intro h
  cases h

example : ¬(IsEven 3) :=
  fun h ↦
    match h with
    | IsEven.addTwoEven h' =>
      nomatch h'

example : ¬(IsEven 3) := by
  intro h
  cases h with
  | addTwoEven h' =>
    cases h'


/--
Twice any natural number is even.
-/
theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by -- starts tactic mode for theorem `IsEven_two_mul`; the following tactics prove the stated goal
  induction n with
  | zero => apply zeroEven -- applies `zeroEven` backwards, replacing the current goal by its premises
  | succ m ih =>
     apply addTwoEven
     assumption -- performs induction on `n` and sends each base/step goal to `grind`

/--
The successor of an even number is not even (i.e., it is odd).
-/
theorem succ_odd_of_isEven {n : Nat} -- states and proves theorem `succ_odd_of_isEven`
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction h with
  | zeroEven =>
    show IsEven (0 + 1) → False
    intro h'
    simp at h'
    cases h'
  | addTwoEven h ih =>
    rename_i m
    intro contra
    cases contra with
    | addTwoEven h =>
      contradiction

#print List

/--
For any natural number `n`, either `n` is even or `n + 1` is even.
-/
theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1) -- states and proves theorem `nOrSuccNeven`
  := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction n <;> grind -- performs induction on `n` and sends each base/step goal to `grind`

/--
error: (kernel) arg #1 of 'langur.Paradox.evil' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in -- checks that the following command produces the expected message
inductive Paradox where
 | okay : Paradox
 | evil: (Paradox → Bool) → Paradox

inductive NatTree where
  | leaf : Nat → NatTree
  | node : (Nat → NatTree) → NatTree


#check NatTree.rec (motive := fun _ => Nat)


/-!
## Exercise: Odd numbers

Define an inductive predicate `IsOdd : Nat → Prop` for odd natural numbers, and prove that any natural number is either even or odd, but not both (As two separate propositions).
-/
end langur -- closes the current namespace or section
/-!
## Next files

* `Adder.lean` - typeclasses; instances of typeclasses; typeclass inference. (recommended next file).
-/
