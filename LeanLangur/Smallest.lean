import Mathlib -- imports definitions and theorems used below
/-!
## Prerequisite files

* `IsEven.lean` - inductive propositions and basic use of `grind`.

## Main concepts introduced

* generic smallest-element functions.
* linear-order typeclass parameters.
-/

/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.
-/

namespace langur -- starts a namespace to group the tutorial definitions

namespace general -- starts a namespace to group the tutorial definitions

variable {α : Type} [LinearOrder α]

/--
Implementation of the smallest element in a non-empty list for any type with a linear order.
-/
def smallest  (l: List α) (h: l ≠ []) : α := -- defines `smallest`
  match l with -- splits computation into cases by pattern matching
  | x :: [] => x -- matches a singleton list and returns `x`
  | x :: y :: zs => -- matches a list with at least two elements and returns `min x (smallest (y :: zs) (by simp))`
    min x (smallest (y :: zs) (by simp))

/--
The element returned by `smallest` is indeed a member of the list.
-/
theorem smallest_mem (l: List α) (h: l ≠ []) : -- states and proves theorem `smallest_mem`
    smallest l h ∈ l := by -- starts tactic mode; the following tactics prove the proposition just stated
  fun_induction smallest <;> grind -- follows the recursive equations of `smallest` and lets `grind` solve each generated case

/--
The element returned by `smallest` is less than or equal to all elements in the list.
-/
theorem smallest_le_all (l: List α) (h: l ≠ []) (x: α) : -- states and proves theorem `smallest_le_all`
    x ∈ l → smallest l h ≤ x := by -- starts tactic mode; the following tactics prove the proposition just stated
  fun_induction smallest <;> grind -- follows the recursive equations of `smallest` and lets `grind` solve each generated case

end general -- closes the current namespace or section

/-!
## Exercise: Smallest element for partial orders

Define a function analogous to `smallest` for lists of elements of a type with a partial order, and prove the corresponding properties. You will need to use `DecidableLE` to be able to compare elements in the list, and the definition will use `if` expressions in place of `min`.

One of the above theorems is true for partial orders, but the other is not. Which one is it? Prove the one that is true, and give a counterexample for the one that is not using the partial order on `Nat × Nat`.
-/
namespace partial_order -- starts a namespace to group the tutorial definitions
variable {α : Type} [PartialOrder α][DecidableLE α]

end partial_order -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
