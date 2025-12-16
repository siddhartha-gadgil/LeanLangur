import Std
import Mathlib
open Std

/-!
# Catalan Numbers and Memoization

The Catalan numbers are a sequence of natural numbers that have many combinatorial interpretations.

These satisfy the recurrence relation:
* `C(0) = 1`
* `C(n+1) = Σ (C(i) * C(n-i)) for i = 0 to n`

We can naively implement this recurrence relation in Lean, but it will be inefficient for large `n` due to repeated calculations. We show how to use memoization to optimize the computation of Catalan numbers using `State` Monad.
-/
namespace Catalan

abbrev CatalanM := StateM (HashMap Nat Nat)

#check List.range

/-- Naive recursive computation of Catalan numbers -/
partial def catalanNaive : Nat → Nat
  | 0 => 1
  | n + 1 =>
    let terms :=
      List.range (n + 1) |>.map (fun i => catalanNaive i * catalanNaive (n - i))
    terms.sum

/-- Memoized computation of Catalan numbers using State Monad -/
partial def catalanMemo (n : Nat) : CatalanM Nat := do
  let cache ← get
  match cache.get? n with
  | some value => return value
  | none =>
    match n with
    | 0 =>
      modify (fun m => m.insert 0 1)
      return 1
    | n + 1 =>
      let mut sum := 0
      for i in [0:n + 1] do
        let ci ← catalanMemo i
        let cni ← catalanMemo (n - i)
        sum := sum + (ci * cni)
      modify (fun m => m.insert (n + 1) sum)
      return sum

#eval catalanMemo 23 |>.run' {}
