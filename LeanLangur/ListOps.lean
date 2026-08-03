import Mathlib -- imports definitions and theorems used below
/-!
## Prerequisite files

* `SmallestNat.lean` - functions and proofs and macros and notation.

## Main concepts introduced

* implicit and explicit parameters.
* monadic `do` notation for lists.
-/

/-!
# List operations

We illustrate:

* Explicit and Implicit parameters.
* `do` notation for lists.
* Why we need typeclasses.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
Doubles a list by concatenating it with itself.
This version takes the type `α` as an explicit parameter.
-/
def doubleList (α : Type) (l: List α) : List α := -- defines `doubleList`
  l ++ l

#eval doubleList Nat [1, 3 ,5] -- runs this expression as a tutorial check

#eval doubleList String ["hello", "world"] -- runs this expression as a tutorial check

#eval doubleList _ ["a", "b", "c"] -- runs this expression as a tutorial check

/--
error: don't know how to synthesize placeholder for argument `l`
context:
⊢ List ℕ
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval doubleList Nat _ -- runs this expression as a tutorial check

/--
Doubles a list by concatenating it with itself.
This version uses an implicit type parameter `{α : Type}`.
-/
def dblList {α : Type} (l: List α) : List α := -- defines `dblList`
  l ++ l

#eval dblList [1, 3 ,5] -- runs this expression as a tutorial check

#eval @dblList Int [1, 3 ,5] -- runs this expression as a tutorial check

#eval @dblList _ [1, 3 ,5] -- runs this expression as a tutorial check

/-!
List of pairs using `do` notation. The `do` notation is a convenient way to compose operations that involve iterating over lists. It allows us to write code that looks more like a traditional imperative style, while still being purely functional. The same notation and behaviour holds for so-called **Monads** in general. We will encounter other monads later, in particular `State` monads and `Option`.
-/

#check Monad

/--
Computes the Cartesian product of two lists using `do` notation.
Returns a list of all possible pairs `(x, y)` where `x ∈ l₁` and `y ∈ l₂`.
-/
def pairs {α β : Type} (l₁: List α) (l₂: List β) : List (α × β) := do -- defines `pairs`
  let x ← l₁ -- binds an intermediate value for the following expression
  let y ← l₂ -- binds an intermediate value for the following expression
  return (x, y) -- returns this value from the monadic block

def pairs' {α β : Type} (l₁: List α) (l₂: List β) : List (α × β) := -- defines `pairs'`
  l₁.flatMap (fun x ↦ l₂.map (fun y ↦ (x, y))) -- uses `flatMap` and `map` to compute the Cartesian product of two lists

#eval pairs [1, 2] ["a", "b"] -- runs this expression as a tutorial check

/-!
## List as a monad

Firstly, it is a function on types.
-/

#check List -- `List` is a function from Type to Type, i.e., `a ↦ List a`.

namespace ListMonad
/-!
Next, a singleton list is a function from `α` to `List α`.
-/
def pure {α : Type} (x : α) : List α := [x] -- defines `pure`

#check List.map -- `List.map` is a function from `(α → β) → List α → List β`

#eval List.map  (fun (s: String) ↦ s.length) ["hello", "world", "lean"] --this expression as a tutorial check

#eval ["hello", "world", "lean"].map (fun s ↦ s.length) -- this expression as a tutorial check

#check List.flatMap

#eval List.range 5

#eval [1, 3, 5].map List.range

#eval [1, 3, 5].flatMap List.range

#eval List.flatMap  (fun (s: String) ↦ pure s.length) ["hello", "world", "lean"] --this expression as a tutorial check

end ListMonad

/-!
## Option as monad
-/
#print Option
#check Option.map

#eval some 3 |>.map (fun x ↦ x + 1) -- runs this expression as a tutorial check

#eval none |>.map (fun x ↦ x + 1) -- runs this expression as a tutorial check

def half? : Nat → Option Nat
| 0 => some 0
| 1 => none
| n + 2 => half? n |>.map (fun x ↦ x + 1)

#eval half? 10

#eval half? 11 -- runs this expression as a tutorial check

def threeHalfs? (n: Nat) : Option Nat :=
  (half? n).map (fun x ↦ x * 3) -- defines `threeHalfs?`

#eval threeHalfs? 10 -- runs this expression as a tutorial check

#eval threeHalfs? 11 -- runs this expression as a tutorial check

def threeHalfs?₁ (n: Nat) : Option Nat := do -- defines `threeHalfs?₁`
  let x ← half? n -- binds an intermediate value for the following expression
  return x * 3 -- returns this value from the monadic block

def quarter? (n: Nat) : Option Nat := do -- defines `quarter?`
  let x ← half? n -- binds an intermediate value for the following expression
  let y ← half? x -- returns this value from the monadic block
  return y -- returns this value from the monadic block

def myFlatMap {α β : Type} (f : α → Option β) (o : Option α) : Option β := match o with -- splits computation into cases by pattern matching
  | none => none -- matches a missing optional value and returns `none`
  | some x => f x -- matches a present optional value and returns `f x`


#eval quarter? 16 -- runs this expression as a tutorial check

#eval quarter? 15 -- runs this expression as a tutorial check

#eval quarter? 14 -- runs this expression as a tutorial check


/-!
## Exercise

Using the `do` notation, implement a function `innerPairs` that in a special case corresponds to the following Python list comprehension:

```python
[(x, y) for l in [[1, 2], [3, 4]] for x in l for y in l]`
```
More generally, we are given `ll: List (List α)` and we want `innerPairs` to return a list of all pairs `(x, y)` such that `x` and `y` are both elements of the same inner list in `ll`. In the above example, the answer would be `[(1, 1), (1, 2), (2, 1), (2, 2), (3, 3), (3, 4), (4, 3), (4, 4)]`.
-/

/-!
List of sums using `do` notation. Requires the type `α` to have an instance of the `Add` typeclass to tell Lean how to add elements of type `α`. This example is just a preview of using typeclasses.
-/

/--
Computes all possible sums of elements from two lists using `do` notation.
-/
def sums {α : Type}[Add α] (l₁: List α) (l₂: List α ) : List α := do -- defines `sums`
  let x ← l₁ -- binds an intermediate value for the following expression
  let y ← l₂ -- binds an intermediate value for the following expression
  return x + y -- returns this value from the monadic block

end langur -- closes the current namespace or section
/-!
## Next files

Continue to the file `People.lean` to see definitions of structures.
-/
