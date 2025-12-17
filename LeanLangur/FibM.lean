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
