/-!
## Structures

A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.
-/
structure Person where
  name : String
  age  : Nat
  deriving Repr, DecidableEq
