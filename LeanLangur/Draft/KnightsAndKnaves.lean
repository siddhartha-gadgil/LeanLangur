import Lean
import ProofWidgets

open Lean Elab Parser Command Meta Macro ProofWidgets Tactic

/-!

# Knights and Knaves Puzzles

A formalization of [Knights and Knaves puzzles](https://en.wikipedia.org/wiki/Knights_and_Knaves)
using Lean automation and a custom Domain Specific Language (DSL).

Puzzles are sourced from the following collection: https://philosophy.hku.hk/think/logic/knights.php.

-/

open Jsx in
#html <iframe src="https://philosophy.hku.hk/think/logic/knights.php" width="600" height="600"></iframe>

@[grind]
inductive Islander where
  | knight
  | knave

@[grind]
def Islander.says (islander : Islander) (statement : Prop) :=
  match islander with
  | .knight => statement
  | .knave => ¬statement

abbrev Islander.isKnight (islander : Islander) : Prop :=
  islander = .knight

abbrev Islander.isKnave (islander : Islander) : Prop :=
  islander = .knave

example (Zoey Mel : Islander)
  (zoey_statement : Zoey.says Mel.isKnave)
  (mel_statement : Mel.says (¬ Zoey.isKnave ∧ ¬Mel.isKnave)) :
  Zoey.isKnight ∧ Mel.isKnave := by
  grind

example (Alice Rex Bob : Islander)
  (alice_statement : Alice.says Rex.isKnave)
  (rex_statement : Rex.says ¬Bob.isKnave)
  (bob_statement : Bob.says (Alice.isKnight ∨ Bob.isKnight)) :
  Alice.isKnave ∧ Rex.isKnight ∧ Bob.isKnight := by
  grind

declare_syntax_cat sentence

syntax (name := is_knave) ident " is " " a " " knave " : sentence

syntax (name := is_knight) ident " is " " a " " knight " : sentence

syntax (name := statement) ident " says " sentence : sentence

syntax (name := parens) "(" sentence ")" : sentence

syntax (name := not) " not " sentence : sentence

syntax (name := and) sentence " and " sentence : sentence

syntax (name := or) sentence " or " sentence : sentence

syntax (name := solve) "SOLVE" : sentence

partial def sentenceToTerm {M} [Monad M] [MonadQuotation M] : TSyntax `sentence → M Term
  | `(sentence| $person:ident is a knave) =>
      `(term| Islander.isKnave $person)
  | `(sentence| $person:ident is a knight) =>
      `(term| Islander.isKnight $person)
  | `(sentence| $person:ident says $stmt:sentence) => do
      `(term| Islander.says $person $(← sentenceToTerm stmt))
  | `(sentence| ( $stmt:sentence )) => sentenceToTerm stmt
  | `(sentence| not $stmt:sentence) => do
      `(term| ¬ $(← sentenceToTerm stmt))
  | `(sentence| $stmt1:sentence and $stmt2:sentence) => do
      `(term| $(← sentenceToTerm stmt1) ∧ $(← sentenceToTerm stmt2))
  | `(sentence| $stmt1:sentence or $stmt2:sentence) => do
      `(term| $(← sentenceToTerm stmt1) ∨ $(← sentenceToTerm stmt2))
  | `(sentence| SOLVE) => `(term| False)
  | _ => panic! "Unexpected syntax: {stx}"

declare_syntax_cat sentences
syntax (name := conclusion) sentence noWs "." : sentences
syntax (name := connector) sentence noWs "." ws sentences : sentences

partial def sentencesToTerm {M} [Monad M] [MonadQuotation M] : TSyntax `sentences → M Term
  | `(sentences| $s:sentence.) => sentenceToTerm s
  | `(sentences| $s:sentence. $ss:sentences) => do `(term| $(← sentenceToTerm s) → ($(← sentencesToTerm ss)))
  | _ => panic! "Unexpected syntax: {stx}"


elab "knights_and_knaves" : tactic => do
  let mainGoal ← getMainGoal
  Grind.withProtectedMCtx (abstractProof := false) mainGoal fun goal => do
    let result ← Grind.main goal (← mkGrindParams {} (only := true) #[← `(grindParam| Islander), ← `(grindParam| Islander.says)] goal)
    let .some result := result.failure? | return
    result.mvarId.withContext do
      let eqcs := result.getEqcs (sort := true)
      let some knights := eqcs.find? (·.contains (.const ``Islander.knight [])) | throwError "No knights found"
      let knights := knights.filter (· != .const ``Islander.knight [])
      let some knaves := eqcs.find? (·.contains (.const ``Islander.knave [])) | throwError "No knaves found"
      let knaves := knaves.filter (· != .const ``Islander.knave [])
      logInfo m!"Knights: {knights}"
      logInfo m!"Knaves: {knaves}"
      let knightSentences ←
        knights.filterMapM (fun | .fvar person => do pure (some s!"{← person.getUserName} is a knight") | _ => pure none)
      let knaveSentences ←
        knaves.filterMapM (fun | .fvar person => do pure (some s!"{← person.getUserName} is a knave") | _ => pure none)
      let mainSentence : String := .join <| (knightSentences ++ knaveSentences).intersperse " and "
      let stx ← getRef
      let solveSpan? := stx.find? (·.getAtomVal = "SOLVE")
      TryThis.addSuggestion stx { suggestion := .string mainSentence } (origSpan? := solveSpan?)
        (header := "Replace \"SOLVE\" with the solution:")

syntax "[" "PUZZLE" ident "]" sentences : command

macro_rules
  | `([PUZZLE $name:ident] $ss:sentences) => do
    `(command| theorem $name : $(← sentencesToTerm ss) := by knights_and_knaves)

[PUZZLE Puzzle1]
  Zoey says Mel is a knave.
  Mel says ((not Zoey is a knave) and (not Mel is a knave)).
  Zoey is a knight and Mel is a knave.
