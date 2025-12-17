/-!
A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.
-/
structure Person where
  name : String
  age  : Nat
  deriving Repr, Inhabited

def examplePerson : Person := {
  name := "Alice",
  age := 30
}

#eval examplePerson.name -- evaluates to "Alice"
#eval examplePerson.age  -- evaluates to 30

#eval examplePerson -- evaluates to { name := "Alice", age := 30 }


structure Voter extends Person where
  voterId : String
  voting_age : age ≥ 18
  deriving Repr

def exampleVoter : Voter := {
  name := "Bob",
  age := 45,
  voterId := "V123456",
  voting_age := by decide
}
