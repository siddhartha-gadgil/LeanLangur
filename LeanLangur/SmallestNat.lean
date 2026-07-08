import Mathlib -- imports definitions and theorems used below
/-!
## Background and Concepts introduced in this file

This is the first file in the tutorial proper. However, there are three preliminary files that introduce some of the foundations of Lean.

* `SimpleTerms.lean` - simple terms, types, and evaluation.
* `PropsProofs.lean` - propositions and proofs - "propositions as types".
* `SumToN.lean` - a simple example of a program and its correctness proof, with some tactics.

We assume that you are familiar with proving using tactics in Lean, as covered in *A glimpse of Lean* even before starting these files. If you are not, you may want to start with the many excellent resources on that topic.
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
Returns `0` for an empty list.
-/
def smallestI (l: List Nat) : Nat := -- defines `smallestI`
  match l with -- splits computation into cases by pattern matching
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: zs => -- matches a list with head `x` and nonempty tail `y :: zs`, then returns the smaller of `x` and the recursive result
    min x (smallestI (y :: zs))
  | [] => 0  -- placeholder for empty list

#eval smallestI [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 1
/--
Implementation of the smallest element in a list of natural numbers.
Returns `0` with error for an empty list.
-/
def smallest! (l: List Nat) : Nat := -- defines `smallest!`
  match l with -- splits computation into cases by pattern matching
  | [x] => x -- matches a singleton list and returns `x`
  | x :: y :: zs => -- matches a list with head `x` and nonempty tail `y :: zs`, then returns the smaller of `x` and the recursive result
    min x (smallest! (y :: zs))
  | [] => panic! "smallest!: empty list"  -- raises an error for empty list

#eval smallest! [3, 1, 4, 1, 5, 9, 2, 6, 5] -- evaluates to 1

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

example :
  smallest [1, 2] (by simp) =
    smallest [1, 2] (by decide) := by
      rfl -- shows that the proof term is independent of the proof of non-emptiness

example (n: Nat) (h : n = m)
    (h' : m = 2) : n * n = 4 := by
  rw [h] -- rewrites `n` to `m` in the goal
  rw [h']

example (n: Nat) (h : m = n)
    (h' : m = 2) : n * n = 4 := by
  rw [← h] -- rewrites `n` to `m` in the goal
  rw [h']

def transport (A B: Type) (h : A = B) (a: A) : B := by
  rw [← h]
  exact a

example  (A B: Type) (h : A = B) (a: A) : B := by
  rw [h] at a
  exact a

#check Eq.mp

example  (A B: Type) (h : A = B) (a: A) : B :=
  Eq.mp h a

def transport' (A B: Type) (h : A = B) (a: A) :
  B := h ▸ a

#print transport' -- prints Lean's generated declaration for inspecti

theorem transportProp (A B: Prop) (h : A = B) (a: A) : B := by
  rw [← h]
  exact a


theorem smallest_mem' (l: List Nat) (h: l ≠ []) : -- states and proves theorem `smallest_mem`
    smallest l h ∈ l := by match l with
  | x :: [] =>
    unfold smallest
    simp only [List.mem_cons, List.not_mem_nil, or_false]  -- base case: if the list is a singleton, the smallest is that element, which is trivially in the list
  | x :: y :: zs => -- inductive case: if the list has at least
    simp only [smallest, List.mem_cons, inf_eq_left]
    have ih := smallest_mem' (y :: zs) (by simp) -- induction hypothesis: the smallest of the tail is in the tail
    grind

-- set_option trace.grind.debug true in
example (l: List Nat) (h: l ≠ []) : -- states and proves theorem `smallest_mem`
    smallest l h ∈ l := by
    fun_induction smallest
    · -- focus on the first case
      simp
    · -- focus on the second case
      grind

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

-- #eval smallest% []

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

Continue to `ListOps.lean` to see implicit parameters and some examples of `do` notation.
-/
