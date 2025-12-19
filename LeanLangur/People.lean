/-!
## Structures

A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.
-/
structure Person where
  name : String
  age  : Nat
  deriving Repr, DecidableEq

def alice : Person :=
  { name := "Alice", age := 30 }

#eval alice.name  -- evaluates to "Alice"
#eval alice.age   -- evaluates to 30
#eval alice        -- { name := "Alice", age := 30 }

structure Voter extends Person where
  voterId : Nat
  is_voting_eligible : 18 ≤ age
  deriving Repr, DecidableEq

def bob : Voter :=
  { name := "Bob", age := 25, voterId := 12345, is_voting_eligible := by simp }
