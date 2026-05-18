/-!
## Prerequisite files

* None in the README dependency diagram.

## Main concepts introduced

* Lean worksheet commands with `#eval` and `#check`.
* simple definitions.
-/

/-!
## Using Lean

The most common way to run Lean is using VS Code with the Lean extension. This is an experience similar to a worksheet/notebook. The `#eval` commands can be run to see their output and `#check` commands can be run to see the type of an expression.
-/

namespace langur -- starts a namespace to group the tutorial definitions

#eval 1 + 2 -- evaluates to 3

def hello := "world" -- defines `hello`

#eval "Hello, " ++ hello -- evaluates to "Hello, world"

#check hello -- checks the type of `hello`, which is `String`

/-!
The following is for importing to make termination proofs easier in later files. You can ignore it for now.
-/
macro_rules | `(tactic | decreasing_trivial) => `(tactic | grind) -- adds a macro expansion rule

end langur -- closes the current namespace or section
/-!
## Next files

* `SmallestNat.lean` - functions and proofs; macros and notation.
-/
