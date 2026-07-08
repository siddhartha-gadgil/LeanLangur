import Mathlib
/-!
# Recursive functions and inductive propositions

Recursion and induction are fundamental concepts in programming and mathematics.
In functional programming languages like Lean, the only (direct) form of loop is recursion.

As an example, we define recursively summing to `n` and prove a theorem about it.
-/

/--
The function `sumToN` computes the sum of the first `n` natural numbers.
-/
def sumToN (n: Nat) : Nat := -- defines a function named `sumToN` that takes a natural number and returns a natural number
  match n with -- splits the computation into cases according to the shape of `n`
  | 0 => 0 -- the sum up to `0` is `0`
  | m + 1 => -- handles the successor case, where `n` is one more than some natural number `m`
    (sumToN m) + (m + 1) -- recursively sums up to `m`, then adds the final number `m + 1`

#eval sumToN 10 -- 55

namespace concise -- starts a namespace containing a shorter version of the same definition
def sumToN : Nat → Nat -- defines `sumToN` directly as a function from natural numbers to natural numbers
| 0 => 0 -- the base case returns `0`
| m + 1 => (sumToN m) + (m + 1) -- the recursive case adds the current number to the sum up to `m`
end concise -- closes the `concise` namespace

/--
The theorem `sumToN_eq` states that the sum of the first `n` natural numbers is `n * (n + 1) / 2`.
-/
theorem sumToN_eq (n: Nat) : 2 * sumToN n = n * (n + 1) := by -- states and begins a proof of the closed-form formula for twice `sumToN n`
  induction n with -- proves the theorem by induction on the natural number `n`
  | zero => rfl -- proves the base case by reflexivity after computation
  | succ m ih => grind [sumToN] -- proves the successor case using the induction hypothesis and the definition of `sumToN`

#check List.foldl

def sumToN_foldl (n: Nat) : Nat := -- defines `sumToN_foldl` using a left fold over a list of natural numbers
  List.foldl (fun acc x ↦ acc + x) 0 (List.range (n + 1)) -- folds the addition function over the list of numbers from `0` to `n`, starting with an accumulator of `0`

def sumToNImp (n: Nat) := Id.run do -- defines `sumToNImp` using imperative-style programming with `do` notation
  let mut acc := 0 -- initializes a mutable accumulator variable to `0`
  for x in List.range (n + 1) do -- iterates over the list of numbers from `0` to `n`
    acc := acc + x -- updates the accumulator by adding the current number
  return acc -- returns the final value of the accumulator

#eval sumToNImp 10 -- evaluates to 55

def sumToNImp' (n: Nat) := Id.run do -- defines `sumToNImp` using imperative-style programming with `do` notation
  let mut sum := 0 -- initializes a mutable accumulator variable to `0`
  let mut i := 0
  while i < n  do -- iterates over the list of numbers from `0` to `n`
    i := i + 1
    sum :=
      sum +
      i -- updates the accumulator by adding the current number
  return sum -- returns the final value of the accumulator

#eval sumToNImp' 10 -- evaluates to 55
