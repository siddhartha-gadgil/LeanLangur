import Lean
import Mathlib

open Lean Meta Elab Parser Tactic

namespace LeanAide
/-!
Code from Lean 4 copied, simplified and customized. The main change is that instead of parsing the imports the current environment is used. In the entry point `simpleRunFrontend` the environment is passed as an argument.

In the `runFrontendM` function the environment is modified if the `modifyEnv` flag is set to true. The `elabFrontDefValueM` function is used to get the value of a definition in the environment. The `checkElabFrontM` function is used to check if the code has any errors.
-/

def simpleRunFrontend
    (input : String)
    (env: Environment)
    (opts : Options := {}) (top : String := "universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u₁ u₂ u₃
set_option maxHeartbeats 10000000
open scoped Nat
")
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := unsafe do
  let inputCtx := Parser.mkInputContext (top ++ input) fileName
  let commandState := Command.mkState env (opts := opts)
  let parserState: ModuleParserState := {}
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env, s.commandState.messages)

def runFrontendForMessagesM (input: String) : MetaM (List String) := do
  let (_, msgs) ← simpleRunFrontend input (← getEnv)
  msgs.toList.mapM (·.toString)

def getTryThisTacticText? (input: String) : MetaM (Option String) := do
  let msgs ← runFrontendForMessagesM input
  msgs.findSomeM? fun s =>
    if s.startsWith "Try this:" || s.startsWith "Try these:" then
      return (s.splitOn "[apply] ")[1]?
    else
      return none

declare_syntax_cat tacticSeqCategory
syntax tacticSeq : tacticSeqCategory

def getTryThisTactic? (input: String) : MetaM (Option (TSyntax ``tacticSeq)) := do
  let tacticText? ← getTryThisTacticText? input
  tacticText?.bindM fun tacticText => do
    let stx? := runParserCategory (← getEnv) `tacticSeqCategory tacticText
    match stx? with
    | Except.ok stx =>
      logInfo m!"Parsed suggested tactic: {stx}"
      match stx with
      | `(tacticSeqCategory| $ts:tacticSeq) =>
        return some ts
      | _ =>
        logError m!"Unexpected syntax format for suggested tactic: {stx}"
        return none
    | Except.error e =>
      logError m!"Failed to parse suggested tactic; {e}:\n{tacticText}"
      return none

#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by grind? "


#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + 1 := by exact? "

#eval runFrontendForMessagesM "example (n : Nat) : n ≤ n + n := by grind? "

example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind?

#eval runFrontendForMessagesM "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind? "

#eval getTryThisTacticText? "example (n : Nat) : n ≤ n + 1 := by exact? "

#eval getTryThisTacticText? "example (n : Nat) : n ≤ n + n := by grind? "

example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind?

#eval getTryThisTactic? "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind? "

#eval getTryThisTactic? "example (n : Nat) : n ≤ n + 1 := by exact? "

#eval getTryThisTactic? "example (n : Nat) : n ≤ n + n := by grind? "

example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind?

#eval getTryThisTactic? "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  grind? "

example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  aesop?

#eval getTryThisTactic? "example (x : Nat) : 0 < match x with
  | 0   => 1
  | n+1 => x + n := by
  aesop? "

end LeanAide
