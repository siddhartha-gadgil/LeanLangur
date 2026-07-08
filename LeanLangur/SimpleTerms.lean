/-!
# Foundations of Lean: Simple Terms and Types

* "Everything" in Lean is a term. Terms have types.
* Terms include:
  * numbers, strings
  * functions
  * lists
  * propositions (logical statements)
  * proofs
  * types
* We can form expressions for terms and types.
* We make two kinds of *judgements*:
  * term `a` has type `α`.
  * terms `a` and `b` are equal by definition.

## Simple Terms and Types

We consider a few terms and types in Lean. These are definitions that do not involve recursion/induction or propositions.

The `#check` command displays the type of a term. The `#eval` command evaluates a term to a value if this makes sense.
-/

-- We can build simple terms using *literals* for numbers and strings and the usual arithmetic and string operations.
#eval 2 + 3 -- 5

-- Addition of natural numbers is a term of type `Nat`.
#check 2 + 3 -- Nat

#check "Hello, Lean!" -- String

-- We can specify the type of a term using a *type annotation*. For example, we can specify that `2` is an integer rather than a natural number.
#check (2: Int) + 3 -- Int

-- The types `Nat` and `Int` are themselves terms of type `Type`.
#check Nat -- Type

#check Int -- Type

-- The type `Type` is itself a term of type `Type 1`. This is an example of a *universe* in Lean. We will discuss universes later.
#check Type -- Type 1

/-!
We can define new terms using `def`. We can also use `#check` and `#eval` on defined terms.
-/
def two : Nat := 2

-- We can use the defined term `two` in other definitions.
def five := two + 3

-- We can check the types of the defined terms.
#check two -- Nat

#check five -- Nat

-- We can evaluate the defined terms.
#eval five -- 5

/-!
## Function types

If `α` and `β` are types, then `α → β` is the type of functions from `α` to `β`.
-/
#check Nat → Nat -- Type

/--
The cube of a natural number.
-/
def cube (n: Nat) : Nat := n * n * n

-- We can check the type of `cube` and evaluate it at an argument.
#check cube -- Nat → Nat

#eval cube 3 -- 27

-- We can only evaluate terms of types for which we have a nice string representation.
/--
error: could not synthesize a `Repr` or `ToString` instance for type
  Nat → Nat
-/
#guard_msgs in
#eval cube

/-
def cube : Nat → Nat :=
fun n ↦ n * n * n
-/
#print cube

/--
The cube of a natural number, using a lambda expression.
-/
def cube' : Nat → Nat :=
  fun n ↦ n * n * n -- can use `=>` instead of `↦`

#eval cube' 3 -- 27

/-!
The right hand side of the definition of `cube'` is a lambda expression. This is an expression giving a term in Lean, and it has type `Nat → Nat`.
We can even evaluate the lambda expression at an argument to get a value.
-/
#check fun n ↦ n + 2 -- Nat → Nat

#eval (fun n ↦ n + 2) 5 -- evaluates the function at `5` to `7`


/--
The cube of a natural number, using a lambda expression with argument type specified.
-/
def cube'' := fun (n : Nat) ↦ n * n * n
#check cube'' -- Nat → Nat

example :
  (fun (x : Nat) ↦ x + 1) = fun (y : Nat) ↦ y + 1 := rfl

/-!
## Curried functions

Suppose we want to define the function `f` of two variables `a` and `b` taking value `a + b + 1`. We can define it as a function of one variable `a` returning a function of one variable `b`.
-/

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, defined as an iterated lambda.
-/
def sum_of_squares : Nat → Nat → Nat :=
  fun a ↦ fun b ↦ a * a + b * b

#eval sum_of_squares 3 4 -- 25

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using arguments in a single pair of parentheses.
-/
def sum_of_squares' (a b : Nat) : Nat :=
  a * a + b * b

#eval sum_of_squares' 3 4 -- 25

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using a lambda expression with two arguments.
-/
def sum_of_squares'' : Nat → Nat → Nat :=
  fun a b ↦ a * a + b * b

/--
The function of two variables `a` and `b` taking value `a * a + b * b`, using a lambda expression with two arguments and type annotations for one. The other type is inferred.
-/
def sum_of_squares'''  :=
  fun (a : Nat) b ↦ a * a + b * b

#check sum_of_squares''' -- Nat → Nat → Nat

example :=
    fun (a : Nat) (b : Int) ↦ a * a + b * b
