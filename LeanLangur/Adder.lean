/-!
## Prerequisite files

* `ListOps.lean` - implicit and explicit parameters and monadic `do` notation for lists.

## Main concepts introduced

* typeclasses.
* custom `Add` instances.
* typeclass inference.
-/

/-!
# `Add` typeclass

We illustrate:

* How to use addition in the presence of the typeclass `Add`.
* How to create new instances of `Add` for custom types.
* Typeclass inference.

-/

namespace langur -- starts a namespace to group the tutorial definitions

#eval 3 + 4 -- runs this expression as a tutorial check

#eval "hello " ++ "world" -- runs this expression as a tutorial check

open Add -- opens names so constructors or helpers can be written unqualified
#eval add 1 3 -- runs this expression as a tutorial check

#check add -- asks Lean to display the inferred type

/--
error: failed to synthesize instance of type class
  Add String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval add "Hello" "world" -- runs this expression as a tutorial check

instance : Add String where -- provides an instance for typeclass search
  add s t := s ++ " " ++ t

#eval add "Hello" "world" -- runs this expression as a tutorial check

#eval "Hello" + "world" -- runs this expression as a tutorial check

instance {α β : Type}[Add α][Add β] : -- provides an instance for typeclass search
  Add (α × β) where
  add := fun (a₁, b₁) (a₂, b₂) ↦
      (a₁ + a₂, b₁ + b₂)

#eval (1, 2, "Hello") +(3, 4, "world") -- runs this expression as a tutorial check

/-!
## Exercise: Pointwise addition

Given a function `f: α → β` and a typeclass `Add β`, we can define pointwise addition on functions. Implement the instance of `Add (α → β)` that defines pointwise addition on functions. If correct, you should be able to uncomment the example below so it compiles.
-/


-- example : (fun x ↦ x + 1) + (fun x ↦ x * 2) = (fun x ↦  x + 1 + (x * 2)) := by
--   funext x
--   rfl

end langur -- closes the current namespace or section
/-!
## Next files

* `Largest.lean` - programs with proofs; nonempty-list algorithms over linear orders.
* `FunEquality.lean` - equality of functions; decision procedures; proof irrelevance.
* `FibM.lean` - memoization; the `State` monad.
-/
