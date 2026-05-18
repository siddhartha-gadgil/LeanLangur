import Mathlib -- imports definitions and theorems used below
/-!
## Prerequisite files

* `Basic.lean` - Lean worksheet commands with `#eval` and `#check` and simple definitions.

## Main concepts introduced

* functions and proofs.
* macros and notation.
-/

/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.

This module is a good starting point for learning how to write simple programs and proofs in Lean 4. The only background required is basic Lean proving as in *A glimpse of Lean*.
-/

namespace langur -- starts a namespace to group the tutorial definitions

namespace nat -- starts a namespace to group the tutorial definitions

/--
A simple, incomplete implementation of the smallest element in a list of natural numbers.
Returns `default` (0) for an empty list.
-/
def smallestI (l: List Nat) : Nat := -- defines `smallestI`
  match l with -- splits computation into cases by pattern matching
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: zs => -- matches a list with head `x` and nonempty tail `y :: zs`, then returns the smaller of `x` and the recursive result
    min x (smallestI (y :: zs))
  | [] => default  -- placeholder for empty list

#eval smallestI [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 1

/--
Implementation of the smallest element in a non-empty list of natural numbers.
The non-emptiness is guaranteed by the hypothesis `h`.
-/
def smallest (l: List Nat) (h: l ≠ []) : Nat := -- defines `smallest`
  match l with -- splits computation into cases by pattern matching
  | x :: [] => x -- matches a singleton list and returns `x`
  | x :: y :: zs => -- matches a list with head `x` and nonempty tail `y :: zs`, then returns the smaller of `x` and the recursive result
    min x (smallest (y :: zs) (by simp))

/--
The element returned by `smallest` is indeed a member of the list.
-/
theorem smallest_mem (l: List Nat) (h: l ≠ []) : -- states and proves theorem `smallest_mem`
    smallest l h ∈ l := by -- starts tactic mode; the goal is to prove the computed smallest element occurs in `l`
  fun_induction smallest <;> grind -- `fun_induction` creates one goal for each recursive clause of `smallest`; `grind` solves each membership goal

/--
The element returned by `smallest` is less than or equal to all elements in the list.
-/
theorem smallest_le_all (l: List Nat) (h: l ≠ []) (x: Nat) : -- states and proves theorem `smallest_le_all`
    x ∈ l → smallest l h ≤ x := by -- starts tactic mode; the goal is to show every list member is at least the computed smallest element
  fun_induction smallest <;> grind -- `fun_induction` follows the recursion of `smallest`; `grind` uses the induction hypotheses and `min` facts

#eval smallest [3, 1, 4, 1, 5, 9, 2, 6, 5] (by simp) -- evaluates to 1

/--
A macro to call `smallest` and automatically discharge the non-emptiness proof for literals.
-/
macro "smallest%" l:term : term => do -- declares a custom macro form
  `(smallest $l (by simp))

#eval smallest% [3, 1, 4, 1, 5, 9, 2, 6, 5] -- evaluates to 1

#print smallest_mem -- prints Lean's generated declaration for inspection

#print smallest_mem._proof_1_2 -- prints Lean's generated declaration for inspection
#print smallest_mem._proof_1_3 -- prints Lean's generated declaration for inspection
#print smallest.induct_unfolding -- prints Lean's generated declaration for inspection

/-!
## Exercise: smallest element of a filtered list

Prove that if `p` is a predicate on natural numbers and `l` is a list of natural numbers such that the filtered list `l.filter p` is non-empty, then the smallest element of `l` is less than or equal to the smallest element of `l.filter p`.

It will be useful to use the above results. Think about the mathematical argument for this fact, and then try to translate it into Lean. You may find it helpful to introduce some intermediate variables and hypotheses to structure the proof.
-/
theorem smallest_le_smallest_of_filter (l: List Nat) (p: Nat → Bool) (h: l.filter p ≠ []) : -- states and proves theorem `smallest_le_smallest_of_filter`
  smallest l (by grind) ≤ smallest (l.filter p) h := by -- starts tactic mode; the goal compares the smallest element of `l` with that of its nonempty filtered sublist
  sorry

end nat -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* `ListOps.lean` - implicit and explicit parameters; monadic `do` notation for lists.
* `FibM.lean` - memoization; the `State` monad.
-/
