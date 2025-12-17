import Mathlib.Order.Lattice
/-!
## Largest Element in a List: Programs with Proofs

We illustrate how to write programs with proofs in Lean by implementing a function to find the largest element in a (non-empty) list, along with proofs that the element is indeed in the list and is larger than or equal to all other elements.

* We first implement `largestNat` for lists of natural numbers, along with proofs `largestNat_mem` and `largestNat_ge_all`.

* We then generalize this to lists of any type with a linear order, implementing `largest` for *non-empty* lists along with proofs `largest_mem` and `largest_ge_all`.
-/
