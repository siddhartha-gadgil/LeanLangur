/-!
## Using Lean

The most common way to run Lean is using VS Code with the Lean extension. This is an experience similar to a worksheet/notebook. The `#eval` commands can be run to see their output and `#check` commands can be run to see the type of an expression.
-/
#eval 1 + 2 -- evaluates to 3

def hello := "world"

#eval "Hello, " ++ hello -- evaluates to "Hello, world"

#check hello -- checks the type of `hello`, which is `String`
