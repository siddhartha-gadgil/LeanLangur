import Std
/-!
# Fibonacci Numbers with Memoization

The Fibonacci numbers are a classic sequence defined by the recurrence relation:
* `F(0) = 0`
* `F(1) = 1`
* `F(n) = F(n-1) + F(n-2)` for `n ≥ 2`
We can naively implement this recurrence relation in Lean, but it will be inefficient for large `n` due to repeated calculations. We show how to use memoization to optimize the computation of Fibonacci numbers using `State` Monad.

In the specific case of Fibonacci numbers, we can instead just use pairs. But this example illustrates the general technique of memoization using the State monad.
-/
namespace FibM

def slowFib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => slowFib (n + 1) + slowFib n

#eval slowFib 35

open Std

abbrev FibM := StateM (HashMap Nat  Nat)

def fibM (n : Nat) : FibM Nat := do
  let cache ← get
  match cache.get? n with
  | some value => return value
  | none =>
    match n with
    | 0 =>
      modify (fun m => m.insert 0 0)
      return 0
    | 1 =>
      modify (fun m => m.insert 1 1)
      return 1
    | n + 2 =>
      let fn1 ← fibM (n + 1)
      let fn2 ← fibM n
      let result := fn1 + fn2
      modify (fun m => m.insert (n + 2) result)
      return result
#eval fibM 1000 |>.run' {} -- This will be fast due to memoization

end FibM
