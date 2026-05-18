import Mathlib -- imports definitions and theorems used below
/-!
## Prerequisite files

* `CatalanM.lean` - memoized Catalan numbers and stateful dynamic programming.

## Main concepts introduced

* recursive combinatorial definitions.
* factorials.
* state-monad exercises.
-/

open Nat -- opens names so constructors or helpers can be written unqualified
/-!
## Recursive definitions of Combinations

This is an extended exercise with three parts:

1. Use the recursive definition of the number of combinations to define a function `comb : Nat → Nat → Nat` that computes the number of ways to choose `k` elements from a set of `n` elements.
2. Prove that `(comb n k) * (k)! * (n - k)! = (n)!` for all `n` and `k`.
3. Use a state monad to implement a function that generates all combinations of `k` elements from a list of `n` elements in an efficient way.

Recall that the recursive definition of combinations is given by:

* `comb (n + 1) (k + 1) = comb n k + comb n (k + 1)`
* `comb n 0 = 1`
* `comb 0 (k + 1) = 0`
-/

#check Nat.factorial -- asks Lean to display the inferred type

#eval 3! -- runs this expression as a tutorial check
/-!
## Next files

* None in the README dependency diagram.
-/
