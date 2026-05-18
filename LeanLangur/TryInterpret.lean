import Lean -- imports definitions and theorems used below
import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* `FibM.lean` - memoization and the `State` monad.
* `NonAtom.lean` - constructing typeclasses and typeclass fields and instances.

## Main concepts introduced

* frontend interpretation.
* environment manipulation.
* generated Lean snippets.
-/

namespace langur -- starts a namespace to group the tutorial definitions

open Lean Meta Elab Parser Tactic -- opens names so constructors or helpers can be written unqualified

namespace LeanAide -- starts a namespace to group the tutorial definitions
/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `elabFrontDefValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
-/

def defaultFrontendHeader : String := -- defines `defaultFrontendHeader`
  "universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃\n" ++ -- adds the universe declarations used by snippets
  "set_option maxHeartbeats 10000000\n" ++ -- adds a generous heartbeat limit for generated examples
  "open scoped Nat\n" -- opens natural-number scoped notation in generated examples

def simpleRunFrontend -- defines `simpleRunFrontend`
    (input : String)
    (env: Environment)
    (opts : Options := {}) (top : String := defaultFrontendHeader) -- supplies options and default header text
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := unsafe do
  let inputCtx := Parser.mkInputContext (top ++ input) fileName -- binds an intermediate value for the following expression
  let commandState := Command.mkState env (opts := opts) -- binds an intermediate value for the following expression
  let parserState: ModuleParserState := {} -- binds an intermediate value for the following expression
  let s ← IO.processCommands inputCtx parserState commandState -- binds an intermediate value for the following expression
  pure (s.commandState.env, s.commandState.messages)

def runFrontendForMessagesM (input: String) : MetaM (List String) := do -- defines `runFrontendForMessagesM`
  let (_, msgs) ← simpleRunFrontend input (← getEnv) -- binds an intermediate value for the following expression
  msgs.toList.mapM (·.toString)

def getTryThisTacticText? (input: String) : MetaM (Option String) := do -- defines `getTryThisTacticText?`
  let msgs ← runFrontendForMessagesM input -- binds an intermediate value for the following expression
  msgs.findSomeM? fun s => -- maps this case or syntax pattern to its result
    if s.startsWith "Try this:" || s.startsWith "Try these:" then -- branches on this decidable condition
      return (s.splitOn "[apply] ")[1]? -- returns this value from the monadic block
    else -- handles the alternative branch
      return none -- returns this value from the monadic block

declare_syntax_cat tacticSeqCategory
syntax tacticSeq : tacticSeqCategory -- declares new parser syntax

def tacticsFromText? (tacticText: String) : MetaM (Option (TSyntax ``tacticSeq)) := do -- defines `tacticsFromText?`
  let stx? := runParserCategory (← getEnv) `tacticSeqCategory tacticText -- binds an intermediate value for the following expression
  match stx? with -- splits computation into cases by pattern matching
  | Except.ok stx => -- matches a successful result and logs the matched information before returning
    logInfo m!"Parsed tactics: {stx}"
    match stx with -- splits computation into cases by pattern matching
    | `(tacticSeqCategory| $ts:tacticSeq) => -- matches parsed tactic-sequence syntax and returns it
      return some ts -- returns this value from the monadic block
    | _ => -- matches any remaining form and logs the matched information before returning
      logError m!"Unexpected syntax format for tactics: {stx}"
      return none -- returns this value from the monadic block
  | Except.error e => -- matches a failed result and logs the matched information before returning
    logError m!"Failed to parse tactics; {e}:\n{tacticText}"
    return none -- returns this value from the monadic block

def getTryThisTactic? (input: String) : MetaM (Option (TSyntax ``tacticSeq)) := do -- defines `getTryThisTactic?`
  let tacticText? ← getTryThisTacticText? input -- binds an intermediate value for the following expression
  tacticText?.bindM tacticsFromText?

#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by grind? " -- runs this expression as a tutorial check


#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by exact? " -- runs this expression as a tutorial check

#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + n := by grind? " -- runs this expression as a tutorial check

example (x : Nat) : 0 < match x with -- checks an unnamed example or proof
  | 0   => 1 -- matches zero and returns `1`
  | n+1 => x + n := by -- matches a successor natural number and returns `x + n` as the expression under the inequality
  grind? -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes

#eval runFrontendForMessagesM -- runs this expression as a tutorial check
  ("example (x : Nat) : 0 < match x with\n" ++ -- starts the generated example text
  "  | 0   => 1\n" ++ -- adds the zero branch to the generated text
  "  | n+1 => x + n := by\n" ++ -- adds the successor branch and proof opener
  "  grind? ") -- asks `grind?` to suggest a proof inside the generated text

#eval getTryThisTacticText? "example (n : Nat) : n ≤ n + 1 := by exact? " -- runs this expression as a tutorial check

#eval getTryThisTacticText? "example (n : Nat) : n ≤ n + n := by grind? " -- runs this expression as a tutorial check

example (x : Nat) : 0 < match x with -- checks an unnamed example or proof
  | 0   => 1 -- matches zero and returns `1`
  | n+1 => x + n := by -- matches a successor natural number and returns `x + n` as the expression under the inequality
  grind? -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes

#eval getTryThisTactic? -- runs this expression as a tutorial check
  ("example (x : Nat) : 0 < match x with\n" ++ -- starts the generated example text
  "  | 0   => 1\n" ++ -- adds the zero branch to the generated text
  "  | n+1 => x + n := by\n" ++ -- adds the successor branch and proof opener
  "  grind? ") -- asks `grind?` to suggest a proof inside the generated text

#eval getTryThisTactic? "example (n : Nat) : n ≤ n + 1 := by exact? " -- runs this expression as a tutorial check

#eval getTryThisTactic? "example (n : Nat) : n ≤ n + n := by grind? " -- runs this expression as a tutorial check

example (x : Nat) : 0 < match x with -- checks an unnamed example or proof
  | 0   => 1 -- matches zero and returns `1`
  | n+1 => x + n := by -- matches a successor natural number and returns `x + n` as the expression under the inequality
  grind? -- uses `grind` to combine simplification, constructor facts, and hypotheses until the goal closes

#eval getTryThisTactic? -- runs this expression as a tutorial check
  ("example (x : Nat) : 0 < match x with\n" ++ -- starts the generated example text
  "  | 0   => 1\n" ++ -- adds the zero branch to the generated text
  "  | n+1 => x + n := by\n" ++ -- adds the successor branch and proof opener
  "  grind? ") -- asks `grind?` to suggest a proof inside the generated text

example (x : Nat) : 0 < match x with -- checks an unnamed example or proof
  | 0   => 1 -- matches zero and returns `1`
  | n+1 => x + n := by -- matches a successor natural number and returns `x + n` as the expression under the inequality
  aesop?

#eval getTryThisTactic? -- runs this expression as a tutorial check
  ("example (x : Nat) : 0 < match x with\n" ++ -- starts the generated example text
  "  | 0   => 1\n" ++ -- adds the zero branch to the generated text
  "  | n+1 => x + n := by\n" ++ -- adds the successor branch and proof opener
  "  aesop? ") -- asks `aesop?` to suggest a proof inside the generated text

end LeanAide -- closes the current namespace or section

end langur -- closes the current namespace or section
/-!
## Next files

* None in the README dependency diagram.
-/
