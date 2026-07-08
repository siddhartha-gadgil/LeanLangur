/-!
## Prerequisite files

* `ListOps.lean` - implicit and explicit parameters and monadic `do` notation for lists.
* `People.lean` - structures in lean.

## Main concepts introduced

* typeclasses.
* instances of typeclasses.
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

#check Add

#check add -- asks Lean to display the inferred type
#print Add
#print add

/--
error: failed to synthesize instance of type class
  Add String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval add "Hello" "world" -- runs this expression as a tutorial check

instance addString : Add String where -- provides an instance for typeclass search
  add s t := s ++ " " ++ t

#eval add "Hello" "world" -- runs this expression as a tutorial check

#eval "Hello" + "world" -- runs this expression as a tutorial check

instance : HAdd String Bool String where -- provides an instance for typeclass search
  hAdd s b := if b then s ++ " true" else s ++ " false"

#eval "Hello" + false -- runs this expression as a tutorial check

instance (α : Type) : HAdd α (List α) (List α) where -- provides an instance for typeclass search
  hAdd x xs := x :: xs

#eval 1 + [2, 3]

#eval HAdd.hAdd 1 [2, 3] -- runs this expression as a tutorial check

instance {α β : Type}[Add α][Add β] : -- provides an instance for typeclass search
  Add (α × β) where
  add := fun (a₁, b₁) (a₂, b₂) ↦
      (a₁ + a₂, b₁ + b₂)

#check (1, 2, "Hello")
#eval (1, 2, "Hello") +(3, 4, "world") -- runs this expression as a tutorial check

set_option trace.Meta.synthInstance true in
#synth Add (Nat × Nat × String)

class AddThree (α : Type) where -- declares a new typeclass `AddThree`
  addThree : α → α → α → α -- declares a method `addThree` for the typeclass

def addThree {α : Type} [self: AddThree α] (x y z : α) : α := -- defines a helper function `addThree` that uses the typeclass
  self.addThree x y z

instance : AddThree String where -- provides an instance for typeclass search
  addThree s t u := s ++ " " ++ t ++ " " ++ u

#eval addThree "Hello" "silly" "world" -- runs this expression as a tutorial check

instance {α : Type} [Add α] : AddThree α where -- provides an instance for typeclass search
  addThree x y z := x + y + z

#eval addThree 1 2 3

instance : AddThree Bool where -- provides an instance for typeclass search
  addThree x y z := x || y || z

#eval addThree true false false

#check Zero

instance {α : Type} [AddThree α][Zero α] : Add α  where -- provides an instance for typeclass search
  add := fun x y ↦ addThree x y 0

instance : Zero Bool where -- provides an instance for typeclass search
  zero := false

set_option trace.Meta.synthInstance true in
#eval add true false

#eval (true, 1, "Hello") + (false, 2, "world") -- runs this expression as a tutorial check
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

* `NonAtom.lean` - constructing typeclasses; typeclass fields and instances.
-/
